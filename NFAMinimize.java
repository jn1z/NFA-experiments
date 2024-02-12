import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.IntFunction;

import net.automatalib.alphabet.Alphabet;
import net.automatalib.automaton.base.AbstractCompactSimpleNondet;
import net.automatalib.automaton.fsa.CompactNFA;
import net.automatalib.util.partitionrefinement.Block;
import net.automatalib.util.partitionrefinement.PaigeTarjan;
import org.checkerframework.checker.nullness.qual.Nullable;

public final class NFAMinimize {
    /**
     * NFA minimization in the forward direction, i.e., right-equivalence.
     * @param absAutomaton
     *      original NFA
     * @return
     *      minimized NFA
     */
    static AbstractCompactSimpleNondet<Integer, Boolean> forwardMinimize(
            AbstractCompactSimpleNondet<Integer, Boolean> absAutomaton) {
        final PaigeTarjan pt = new PaigeTarjan();

        // initial classification by accepting states
        initNondeterministic(pt, absAutomaton, absAutomaton::getStateProperty);

        pt.initWorklist(false);
        pt.computeCoarsestStablePartition();

        return toNFAPruned(pt,
                absAutomaton.getInputAlphabet(),
                absAutomaton,
                absAutomaton::getStateProperty);
    }

    /**
     * NFA minimization in the backward direction, i.e., left-equivalence.
     * @param absAutomaton
     *      original NFA
     * @return
     *      minimized NFA
     */
    static AbstractCompactSimpleNondet<Integer, Boolean> backwardMinimize(
            AbstractCompactSimpleNondet<Integer, Boolean> absAutomaton) {

        AbstractCompactSimpleNondet<Integer, Boolean> reverseAutomaton = NFAUtils.reverse(absAutomaton);

        final PaigeTarjan pt = new PaigeTarjan();

        // initial classification by accepting states
        initNondeterministic(pt, reverseAutomaton, reverseAutomaton::getStateProperty);
        //initCompleteNFAPrune(pt, absAutomaton, absAutomaton::getStateProperty);


        pt.initWorklist(false);
        pt.computeCoarsestStablePartition();

        AbstractCompactSimpleNondet<Integer, Boolean> minimalReversed =
                toNFAPruned(pt, reverseAutomaton.getInputAlphabet(), reverseAutomaton, reverseAutomaton::getStateProperty);

        return NFAUtils.reverse(minimalReversed);
    }

    public static int[] initNondeterministic(PaigeTarjan pt,
                                         AbstractCompactSimpleNondet<Integer, Boolean> absAutomaton,
                                         IntFunction<Boolean> initialClassification) {
        if (absAutomaton.getInitialStates().size() != 1) {
            System.out.println("Multiple initial states!");
        }
        assert absAutomaton.getInitialStates().size() == 1; // we only work with one initial state right now

        int numStates = absAutomaton.size();
        int numInputs = absAutomaton.numInputs();

        int sinkId = numStates;
        int numStatesWithSink = numStates + 1;
        int posDataLow = numStatesWithSink;
        int predOfsDataLow = posDataLow + numStatesWithSink;
        int numTransitionsFull = numStatesWithSink * numInputs;
        int predDataLow = predOfsDataLow + numTransitionsFull + 1;

        Block[] blockForState = new Block[numStatesWithSink];

        Map<@Nullable Boolean, Block> blockMap = new HashMap<>();
        int[] statesBuff = new int[numStatesWithSink];
        int statesPtr = 0;

        int init = absAutomaton.getInitialStates().iterator().next(); // "initial state"

        Boolean initClass = initialClassification.apply(init);
        int reachableStates = createOrReuseSuccBlock(
                pt, initClass, blockForState, init, blockMap, statesBuff, 0);

        // Calculate predData size dynamically.
        // In the worst case, it's numTransitions*numStates, but usually, it will be much smaller.
        // This requires creating a temp array for predOfsData, to later copy it into the data array.
        int[] predOfsTemp = new int[numTransitionsFull+1];

        boolean partial = false;

        while (statesPtr < reachableStates) {
            int currId = statesBuff[statesPtr++];
            if (currId == sinkId) {
                continue;
            }
            for (int j = 0; j < numInputs; j++) {
                Set<Integer> successors = absAutomaton.getTransitions(currId, j);
                if (successors.isEmpty()) {
                    // sink state
                    partial = true;
                    reachableStates = createOrReuseSuccBlock(
                            pt, false, blockForState, sinkId, blockMap,
                            statesBuff, reachableStates);
                    predOfsTemp[j * numStatesWithSink + sinkId]++;
                } else {
                    for (int succId : successors) {
                        reachableStates = createOrReuseSuccBlock(
                                pt, initialClassification.apply(succId), blockForState, succId, blockMap,
                                statesBuff, reachableStates);
                        predOfsTemp[j * numStatesWithSink + succId]++;
                    }
                }
            }
        }

        if (partial) {
            for (int j = 0; j < numInputs; j++) {
                predOfsTemp[j*numStatesWithSink + sinkId]++;
            };
        }


        // At this point, predOfsTemp[j*states+i] represents the count of transitions to state i from input j,
        // and predOfsTemp[inputs*states]==0 is padding

        pt.canonizeBlocks();

        // Make offsets cumulative
        predOfsTemp[0] += predDataLow;
        Arrays.parallelPrefix(predOfsTemp, Integer::sum);

        int maxPredSize = predOfsTemp[predOfsTemp.length - 1]; // usually much smaller than numTransitions * numStates
        int minPredSize = predOfsTemp[0];
        int dataSize = minPredSize + (maxPredSize - minPredSize);
        int[] data = new int[dataSize];

        // copy predsOfTemp into data object
        System.arraycopy(predOfsTemp, 0, data, predOfsDataLow, predOfsTemp.length);

        // Iterate over reachable states. Note that statesBuff length may be larger than total states
        for (int i = 0; i < reachableStates; i++) {
            int stateId = statesBuff[i];
            Block b = blockForState[stateId];
            int pos = --b.low;
            data[pos] = stateId; // blockData
            data[posDataLow + stateId] = pos; // posData

            for (int j = 0; j < numInputs; j++) {
                int inputOffset = predOfsDataLow + j*numStatesWithSink;
                if (stateId == sinkId) { // state is new artificial sink
                    int dataOffset = --data[inputOffset + sinkId];
                    data[dataOffset] = stateId; // predData
                } else {
                    Set<Integer> successors = absAutomaton.getTransitions(stateId, j);
                    if (successors.isEmpty()) {
                        // sink state
                        int dataOffset = --data[inputOffset + sinkId];
                        data[dataOffset] = stateId; // predData
                    } else {
                        for (int succId: successors) {
                            assert succId >= 0;
                            int dataOffset = --data[inputOffset + succId];
                            data[dataOffset] = stateId; // predData
                        }
                    }
                }
            }
        }

        pt.setBlockData(data);
        pt.setPosData(data, posDataLow);
        pt.setPredOfsData(data, predOfsDataLow);
        pt.setPredData(data);
        pt.setSize(numStatesWithSink, numInputs);
        pt.setBlockForState(blockForState);

        pt.removeEmptyBlocks();
        return data;
    }

    private static int createOrReuseSuccBlock(
            PaigeTarjan pt, Boolean blockClass, Block[] blockForState, int succId,
            Map<@Nullable Boolean, Block> blockMap, int[] statesBuff, int reachableStates) {
        Block succBlock = blockForState[succId];
        if (succBlock == null) {
            Block block = blockMap.get(blockClass);
            if (block == null) {
                block = pt.createBlock();
                block.high = 0;
                blockMap.put(blockClass, block);
            }
            block.high++;
            blockForState[succId] = block;
            statesBuff[reachableStates++] = succId;
        }
        return reachableStates;
    }

    private static AbstractCompactSimpleNondet<Integer, Boolean> toNFAPruned(
            PaigeTarjan pt,
            Alphabet<Integer> inputs,
            AbstractCompactSimpleNondet<Integer, Boolean> absAutomaton,
            IntFunction<Boolean> spExtractor) {

        // spExtractor tells us whether a state is accepting or not

        if (absAutomaton.getInitialStates().size() != 1) {
            System.out.println("Multiple initial states!");
        }
        assert absAutomaton.getInitialStates().size() == 1; // we only work with one initial state right now
        int origInit = absAutomaton.getInitialStates().iterator().next(); // "initial state"

        int numBlocks = pt.getNumBlocks();
        int numInputs = inputs.size();
        int[] repMap = new int[numBlocks];
        int[] stateMap = new int[numBlocks];
        Arrays.fill(stateMap, -1);

        CompactNFA<Integer> automaton = new CompactNFA<>(inputs);

        //int origInit = absOriginal.getIntInitialState();
        boolean initSp = spExtractor.apply(origInit);
        //int resInit = automaton.addIntInitialState(initSp);
        int resInit = automaton.addInitialState(initSp);

        Block initBlock = pt.getBlockForState(origInit);
        stateMap[initBlock.id] = resInit;
        repMap[resInit] = origInit;

        int statesPtr = 0;
        int numStates = 1;
        while (statesPtr < numStates) {
            int resState = statesPtr++;
            int rep = repMap[resState];
            for (int i = 0; i < numInputs; i++) {
                for (int succ: absAutomaton.getTransitions(rep, i)) {
                    if (succ >= 0) {
                        Block succBlock = pt.getBlockForState(succ);
                        int succBlockId = succBlock.id;
                        int resSucc = stateMap[succBlockId];
                        if (resSucc < 0) {
                            boolean sp = spExtractor.apply(succ);
                            resSucc = automaton.addState(sp);
                            stateMap[succBlockId] = resSucc;
                            repMap[resSucc] = succ;
                            numStates++;
                        }
                        automaton.addTransition(resState, i, resSucc);
                    }
                }
            }
        }

        return automaton;
    }

}

