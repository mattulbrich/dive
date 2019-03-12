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
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.io.File;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * A Reference-graph. Its nodes are References, it is unidirectional and loopless.
 * (adding loops via {@link #addReference(ReferenceTarget, ReferenceTarget)} will throw an
 * {@link UnsupportedOperationException}.)
 * <p>
 * Created by Philipp on 27.08.2017.
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

    /**
     * Computes predecoessors in the reference graph with the type given as className
     *
     * @param source
     * @param className
     * @param <T>
     * @return
     */
    @SuppressWarnings("unchecked")//SaG: ensured by guard
    public <T extends ReferenceTarget> Set<T> allPredecessorsWithType(ReferenceTarget source, Class<T> className) {

        Set<ReferenceTarget> precedingTargets = allPredecessors(source);
        return precedingTargets.stream()
                .filter(referenceTarget -> className.isAssignableFrom(referenceTarget.getClass()))
                .map(it -> (T) it)
                .collect(Collectors.toSet());

    }

    public <T extends ReferenceTarget> Set<T> allSuccessorsWithType(ReferenceTarget source, Class<T> className) {

        Set<ReferenceTarget> precedingTargets = allSuccessors(source);
        return precedingTargets.stream()
                .filter(referenceTarget -> className.isAssignableFrom(referenceTarget.getClass()))
                .map(it -> (T) it)
                .collect(Collectors.toSet());

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
     *
     * @param proof    the current Proof
     * @param parent   the parent ProofNode on which the rule was applied to
     * @param newNodes the List of ProofNodes after rule application
     * @throws RuleException
     */
    public void addFromRuleApplication(Proof proof, ProofNode parent, List<ProofNode> newNodes) throws RuleException {

        ProofNodeSelector proofNodeBefore = new ProofNodeSelector(parent);
        TermReferencesBuilder trb = new TermReferencesBuilder(this, proof, proofNodeBefore);
        for (ProofNode afterNode : newNodes) {
            //get ProofRuleApplication from node
            ProofNodeSelector pns = new ProofNodeSelector(afterNode);
            ProofRuleApplication pra = afterNode.getProofRuleApplication();


            ImmutableList<BranchInfo> branchInfos = pra.getBranchInfo();
            for (BranchInfo bi : branchInfos) {
                //handle replacements
                ImmutableList<Pair<TermSelector, Term>> replacements = bi.getReplacements();
                for (Pair<TermSelector, Term> repl : replacements) {
                    trb.buildReferences(pns, repl.getFst());
                }

            }

        }
    }

    public void addFromScriptNode(ASTNode node, File scriptfile, int linenumber) {
        //TODO
    }


    /**
     * Compute direct parents of type ProofTermReferenceTarget transitively starting at childTarget and ending in the
     * root ProofNode
     *
     * @param childTarget Starting target
     * @param proof       current proof
     * @return Set of parents of childTarget
     */
    public Set<ProofTermReferenceTarget> computeHistory(ProofTermReferenceTarget childTarget, Proof proof) {
        HashSet<ProofTermReferenceTarget> parents = new HashSet<>();
        ProofTermReferenceTarget currentTarget = childTarget;
        parents.addAll(findDirectParents(childTarget, proof));
        //is childtarget part of a reference?
        LinkedList<ProofTermReferenceTarget> toCompute = new LinkedList<ProofTermReferenceTarget>();
        toCompute.add(currentTarget);
        while (toCompute.size() > 0) {
            Set<ProofTermReferenceTarget> directParents = findDirectParents(currentTarget, proof);
            toCompute.addAll(directParents);
            parents.addAll(directParents);
            currentTarget = toCompute.pop();
        }

        return parents;

    }

    /**
     * Find the direct parent of childTarget
     *
     * @param childTarget
     * @param proof
     * @return Set of direct parents of childTarget
     */
    public Set<ProofTermReferenceTarget> findDirectParents(ProofTermReferenceTarget childTarget, Proof proof) {
        HashSet<ProofTermReferenceTarget> parents = new HashSet<>();
        ProofTermReferenceTarget currentTarget = childTarget;
        try {
            if (currentTarget.getProofNodeSelector().getParentSelector() != null && (!this.getGraph().nodes().contains(currentTarget) || this.graph.predecessors(currentTarget).isEmpty())) {
                //currentTarget.getProofNodeSelector().getParentSelector().get(proof).getProofRuleApplication().getBranchInfo()
                ProofTermReferenceTarget parent = new ProofTermReferenceTarget(currentTarget.getProofNodeSelector().getParentSelector(), currentTarget.getTermSelector());
                Term termOfCurrenTarget = computeTermValue(currentTarget.getProofNodeSelector(), currentTarget.getTermSelector(), proof);
                Term termOfParentTarget = computeTermValue(parent.getProofNodeSelector(), parent.getTermSelector(), proof);
                //TODO debug
                System.out.println("Computing parents for: "+ termOfCurrenTarget+ " in Node "+currentTarget.getProofNodeSelector());

                if (termOfCurrenTarget == termOfParentTarget && termOfCurrenTarget != null) {
                    System.out.println("Found parent "+termOfParentTarget+" in Node "+parent.getProofNodeSelector()+ " on same position");
                    parents.add(parent);
                } else {
                    ProofNode proofNode = childTarget.getProofNodeSelector().get(proof);
                    TermSelector childSelector = childTarget.getTermSelector();
                    if(!childSelector.isToplevel()) {
                        //get all changes and check termselectors

                        ImmutableList<BranchInfo> branchInfos = proofNode.getProofRuleApplication().getBranchInfo();
                        branchInfos.forEach(branchInfo -> {
                                    branchInfo.getReplacements().forEach(termSelectorTermPair -> {
                                        if(childSelector.hasPrefix(termSelectorTermPair.getFst())){
                                            //TODO richtig umsetzen, bisher nur näherung
                                          //  Term changedTerm =computeTermValue(currentTarget.getProofNodeSelector().getParentSelector(), termSelectorTermPair.getFst(),proof);
                                            parents.add(new ProofTermReferenceTarget(currentTarget.getProofNodeSelector().getParentSelector(), termSelectorTermPair.getFst()));
                                        }
                                    });
                                }

                        );
                    } else {
                        //TODO neue Position berechenen, weil keine Änderung am Term selber aber an anderen Formeln
                        System.out.println("Did not implement changes in Graph yet");
                        throw new NotImplementedException();
                    }
                }
            } else {

                //Es gibt Vorgänger
                System.out.println("Found an edge in graph, which references parent(s)");
                Set<ProofTermReferenceTarget> proofTermReferenceTargets = allPredecessorsWithType(childTarget, ProofTermReferenceTarget.class);
                parents.addAll(proofTermReferenceTargets);


            }
        } catch (IllegalArgumentException illArg) {
            System.out.println("Could not find element :" + childTarget.getTermSelector() + " of node " + childTarget.getProofNodeSelector() + " in references.");
        } catch (RuleException e) {
            e.printStackTrace();
        }

        return parents;
    }

    private Term computeTermValue(ProofNodeSelector proofNodeSelector, TermSelector termSelector, Proof proof) {
        Term ret = null;
        try {
            ret = termSelector.selectSubterm(proofNodeSelector.get(proof).getSequent());
        } catch (RuleException e) {
            e.printStackTrace();
        }
        return ret;
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
