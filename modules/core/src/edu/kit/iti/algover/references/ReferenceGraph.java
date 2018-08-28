package edu.kit.iti.algover.references;

import com.google.common.graph.EndpointPair;
import com.google.common.graph.Graph;
import com.google.common.graph.GraphBuilder;
import com.google.common.graph.MutableGraph;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import org.antlr.runtime.Token;

import java.util.*;
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

    public Graph<Reference> getGraph() {
        return graph;
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
        if (!graph.nodes().contains(target)) {
            return;
        }
        for (Reference predecessor : getNeighbours.apply(target)) {
            accumSet.add(predecessor);
            // only works when the graph does not have unidirectional cycles.
            // If it doesn't, then at some point getNeighbours is empty and
            // the recursion base case is reached
            accumulateByNeighbouringFunc(accumSet, predecessor, getNeighbours);
        }
    }

    public void addFromReferenceMap(DafnyFile file, Map<TermSelector, DafnyTree> referenceMap) {
        referenceMap.forEach((termSelector, dafnyTree) -> {
            Token start = dafnyTree.getStartToken();
            Token end = dafnyTree.getStopToken();

            CodeReference codeReference = new CodeReference(file, start, end);

            // Code references always point to the root of the proofs
            ProofTermReference termReference = new ProofTermReference(new ProofNodeSelector(), termSelector);

            addReference(codeReference, termReference);
        });
    }

    // TODO
    // implement via TermReferencesBuilder
    public void addFromRuleApplication(Proof proof, ProofNode parent, List<ProofNode> newNodes) throws RuleException {

        ProofNodeSelector proofNodeBefore = new ProofNodeSelector(parent);
        TermReferencesBuilder trb = new TermReferencesBuilder(this, proof, proofNodeBefore);
        for (ProofNode afterNode: newNodes) {
            //get ProofRuleApplication from node
            ProofNodeSelector pns = new ProofNodeSelector(afterNode);
            ProofRuleApplication pra = afterNode.getPsr();

            ImmutableList<BranchInfo> branchInfos = pra.getBranchInfo();
            for (BranchInfo bi : branchInfos) {
                ImmutableList<Pair<TermSelector, Term>> replacements = bi.getReplacements();
                for (Pair<TermSelector, Term> repl : replacements) {
                    trb.buildReferences(pns, repl.getFst());

                }
            }

        }
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder("ReferenceGraph{\n");
        for (EndpointPair<Reference> reference : graph.edges()) {
            builder.append(reference.nodeU());
            builder.append(" -> ");
            builder.append(reference.nodeV());
            builder.append('\n');
        }
        return builder.toString();
    }
}
