package edu.kit.iti.algover.refrenceTypes;

import com.google.common.graph.GraphBuilder;
import com.google.common.graph.MutableGraph;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

/**
 * A Reference-graph. Its nodes are References, it is unidirectional and loopless.
 * (adding loops via {@link #addReference(Reference, Reference)} will throw an
 * {@link UnsupportedOperationException}.)
 * <p>
 * Created by Philipp on 27.08.2017.
 */
public class ReferenceGraph {

    private final MutableGraph<Reference> graph;

    public ReferenceGraph() {
        graph = GraphBuilder.directed().allowsSelfLoops(false).build();
    }

    public void addReference(Reference from, Reference to) {
        graph.putEdge(from, to);
    }

    public Set<Reference> allPredecessors(Reference source) {
        Set<Reference> precedingTargets = new HashSet<>();
        accumulateByNeighbouringFunc(precedingTargets, source, graph::predecessors);
        return precedingTargets;
    }

    public Set<Reference> allSuccessors(Reference source) {
        Set<Reference> successingTargets = new HashSet<>();
        accumulateByNeighbouringFunc(successingTargets, source, graph::successors);
        return successingTargets;
    }

    private void accumulateByNeighbouringFunc(
        Set<Reference> accumSet,
        Reference target,
        Function<Reference, Set<Reference>> getNeighbours) {
        for (Reference predecessor : getNeighbours.apply(target)) {
            accumSet.add(predecessor);
            // only works when the graph does not have unidirectional cycles.
            // If it doesn't, then at some point getNeighbours is empty and
            // the recursion base case is reached
            accumulateByNeighbouringFunc(accumSet, predecessor, getNeighbours);
        }
    }

}
