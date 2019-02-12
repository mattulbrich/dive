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
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import org.antlr.runtime.Token;

import java.io.File;
import java.util.*;
import java.util.function.Function;

/**
 * A Reference-graph. Its nodes are References, it is unidirectional and loopless.
 * (adding loops via {@link #addReference(ReferenceTarget, ReferenceTarget)} will throw an
 * {@link UnsupportedOperationException}.)
 * <p>
 * Created by Philipp on 27.08.2017.
 *
 */
public class ReferenceGraph {

    private final MutableGraph<ReferenceTarget> graph;

    public ReferenceGraph() {
        graph = GraphBuilder.directed().allowsSelfLoops(false).build();
    }

    public Graph<ReferenceTarget> getGraph() {
        return graph;
    }

    public void addReference(ReferenceTarget from, ReferenceTarget to) {
        graph.putEdge(from, to);
    }

    public Set<ReferenceTarget> allPredecessors(ReferenceTarget source) {
        Set<ReferenceTarget> precedingTargets = new HashSet<>();
        accumulateByNeighbouringFunc(precedingTargets, source, graph::predecessors);
        return precedingTargets;
    }

    public Set<ReferenceTarget> allSuccessors(ReferenceTarget source) {
        Set<ReferenceTarget> successingTargets = new HashSet<>();
        accumulateByNeighbouringFunc(successingTargets, source, graph::successors);
        return successingTargets;
    }

    private void accumulateByNeighbouringFunc(
        Set<ReferenceTarget> accumSet,
        ReferenceTarget target,
        Function<ReferenceTarget, Set<ReferenceTarget>> getNeighbours) {
        if (!graph.nodes().contains(target)) {
            return;
        }
        for (ReferenceTarget predecessor : getNeighbours.apply(target)) {
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

            CodeReferenceTarget codeReferenceTarget = new CodeReferenceTarget(file, start, end);

            // Code references always point to the root of the proofs
            ProofTermReferenceTarget termReference = new ProofTermReferenceTarget(new ProofNodeSelector(), termSelector);

            addReference(codeReferenceTarget, termReference);
        });
    }

    /**
     * Add References from rule applications
     * @param proof the current Proof
     * @param parent the parent ProofNode on which the rule was applied to
     * @param newNodes the List of ProofNodes after rule application
     * @throws RuleException
     */
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

    public void addFromScriptNode(ASTNode node, File scriptfile, int linenumber){
        //TODO
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder("ReferenceGraph{\n");
        for (EndpointPair<ReferenceTarget> reference : graph.edges()) {
            builder.append(reference.nodeU());
            builder.append(" -> ");
            builder.append(reference.nodeV());
            builder.append('\n');
        }
        return builder.toString();
    }
}
