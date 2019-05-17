package edu.kit.iti.algover.references;

import com.google.common.graph.EndpointPair;
import com.google.common.graph.Graph;
import com.google.common.graph.GraphBuilder;
import com.google.common.graph.MutableGraph;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import org.antlr.runtime.Token;

import java.io.File;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * A Reference-graph. Its nodes are References, it is unidirectional and loopless.
 * (adding loops via {@link #addReference(ReferenceTarget, ReferenceTarget)} will throw an
 * {@link UnsupportedOperationException}.)
 * <p>
 * @author Created by Philipp on 27.08.2017.
 * @author S. Grebing (enhanced 2019)
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
     * Computes predecessors in the reference graph with the type given as className
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
    @SuppressWarnings("unchecked")//SaG: ensured by guard
    public <T extends ReferenceTarget> Set<T> allSuccessorsWithType(ReferenceTarget source, Class<T> className) {

        Set<ReferenceTarget> precedingTargets = allSuccessors(source);
        return precedingTargets.stream()
                .filter(referenceTarget -> className.isAssignableFrom(referenceTarget.getClass()))
                .map(it -> (T) it)
                .collect(Collectors.toSet());

    }

    /**
     * Computes all successor ReferenceTaregts in the ReferenceGraph for a given ReferenceTarget
     * @param source
     * @return
     */
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
     * Find the direct parent of childTarget in the reference graph
     *
     * @param childTarget
     * @param proof
     * @return Set of direct parents of childTarget
     */
    public Set<ProofTermReferenceTarget> findDirectParents(ProofTermReferenceTarget childTarget, Proof proof) {
        Set<ProofTermReferenceTarget> parents = new HashSet<>();
        ProofTermReferenceTarget currentTarget = childTarget;
        try {
            //There is no predecessor or edge containing the childTarget -> we have to compute the direct parent
            if (currentTarget.getProofNodeSelector().getParentSelector() != null
                    && (!this.getGraph().nodes().contains(currentTarget) || this.graph.predecessors(currentTarget).isEmpty())) {
              //  Logger.getGlobal().info("Did not find predecessor or target in graph. Computing direct parents");
                parents = computeDirectParents(currentTarget, proof);
            } else {
                //We have apredecessor in the graph
            //    Logger.getGlobal().info("Found an edge in graph, which references parent(s)");
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

    /**
     * The case where no predecessor could be found in graph and no edge containing childTarget.
     * Method computes the direct parent by first taking the predecessor node and searching at the same position.
     * If the terms do not coincide, the term was a subterm that was either part of a formula affected by a replacement or
     * the position changed due to addition or deletion of formulas
     *
     * @param currentTarget
     * @param proof
     * @return
     * @throws RuleException
     */
    private Set<ProofTermReferenceTarget> computeDirectParents(ProofTermReferenceTarget currentTarget, Proof proof) throws RuleException {
        Set<ProofTermReferenceTarget> parents = new HashSet<>();
        ProofTermReferenceTarget parent = new ProofTermReferenceTarget(currentTarget.getProofNodeSelector().getParentSelector(), currentTarget.getTermSelector());
        Term termOfCurrenTarget = computeTermValue(currentTarget.getProofNodeSelector(), currentTarget.getTermSelector(), proof);
        Term termOfParentTarget = computeTermValue(parent.getProofNodeSelector(), parent.getTermSelector(), proof);

       // Logger.getGlobal().info("Computing parents for term '" + termOfCurrenTarget + "' in Node " + currentTarget.getProofNodeSelector());

        if (termOfCurrenTarget == termOfParentTarget && termOfCurrenTarget != null) {
       //     Logger.getGlobal().info("Found parent term '" + termOfParentTarget + "' in Node " + parent.getProofNodeSelector() + " on same position");
            parents.add(parent);
        } else {
            ProofNode proofNode = currentTarget.getProofNodeSelector().get(proof);
            TermSelector childSelector = currentTarget.getTermSelector();
            ImmutableList<BranchInfo> branchInfos = proofNode.getProofRuleApplication().getBranchInfo();

            if (!childSelector.isToplevel()) {
                //get all changes and check termselectors
                branchInfos.forEach(branchInfo -> {
                            branchInfo.getReplacements().forEach(termSelectorTermPair -> {
                                if (childSelector.hasPrefix(termSelectorTermPair.getFst())) {
                                    //TODO richtig umsetzen, bisher nur näherung
                                    //  Term changedTerm =computeTermValue(currentTarget.getProofNodeSelector().getParentSelector(), termSelectorTermPair.getFst(),proof);
                                    parents.add(new ProofTermReferenceTarget(currentTarget.getProofNodeSelector().getParentSelector(), termSelectorTermPair.getFst()));
                                }
                            });
                        }

                );
            } else {
                parents.add(handleAddAndDel(proof, parent, childSelector, branchInfos));
            }

        }
        return parents;
    }

    //Currently its a naive implementation
    private ProofTermReferenceTarget handleAddAndDel(Proof proof, ProofTermReferenceTarget parent, TermSelector childSelector, ImmutableList<BranchInfo> branchInfos) throws RuleException {
        //TODO additions

        List<Sequent> additions = new ArrayList<>();
        List<Sequent> deletions = new ArrayList<>();

        branchInfos.forEach(branchInfo -> {
            additions.add(branchInfo.getAdditions());
            deletions.add(branchInfo.getDeletions());
        });
        Sequent parentSeq = parent.getProofNodeSelector().get(proof).getSequent();
        int posInParent = childSelector.getTermNo();
        List<ProofFormula> toCheckAdd = new ArrayList<>();
        for(Sequent s: additions){
            if(childSelector.getToplevelSelector().isAntecedent()){
                s.getAntecedent().forEach(toCheckAdd::add);
                List<TermSelector> termSelectorsAntec  = computeSelector(toCheckAdd, parentSeq, TermSelector.SequentPolarity.ANTECEDENT);
                for(TermSelector sel : termSelectorsAntec){
                    if(sel.getTermNo() < childSelector.getTermNo()){
                        posInParent--;
                    }
                    //this should not happen
                    if(sel.getTermNo() == childSelector.getTermNo()){
                        return new ProofTermReferenceTarget(parent.getProofNodeSelector(), childSelector);
                    }
                }
            } else {
                s.getSuccedent().forEach(toCheckAdd::add);
                List<TermSelector> termSelectorsAntec  = computeSelector(toCheckAdd, parentSeq, TermSelector.SequentPolarity.SUCCEDENT);
                for(TermSelector sel : termSelectorsAntec){
                    if(sel.getTermNo() < childSelector.getTermNo()){
                        posInParent--;
                    }
                    //this should not happen
                    if(sel.getTermNo() == childSelector.getTermNo()){
                        return new ProofTermReferenceTarget(parent.getProofNodeSelector(), childSelector);
                    }

                }
            }
        }


        List<ProofFormula> toCheckDel = new ArrayList<>();
        for(Sequent s: deletions){
            if(childSelector.getToplevelSelector().isAntecedent()){
                s.getAntecedent().forEach(toCheckDel::add);
                List<TermSelector> termSelectorsAntec  = computeSelector(toCheckDel, parentSeq, TermSelector.SequentPolarity.ANTECEDENT);
                for(TermSelector sel : termSelectorsAntec){
                    if(sel.getTermNo() <= childSelector.getTermNo()){
                        posInParent++;
                    }
                }
            } else {
                s.getSuccedent().forEach(toCheckDel::add);
                List<TermSelector> termSelectorsAntec  = computeSelector(toCheckDel, parentSeq, TermSelector.SequentPolarity.SUCCEDENT);
                for(TermSelector sel : termSelectorsAntec){
                    if(sel.getTermNo() <= childSelector.getTermNo()){
                        posInParent++;
                    }
                }
            }
        }
        return new ProofTermReferenceTarget(parent.getProofNodeSelector(), new TermSelector(childSelector.getPolarity(), posInParent));
    }

    private static List<TermSelector> computeSelector(List<ProofFormula> formulas, Sequent seq, TermSelector.SequentPolarity polarity){
        List<TermSelector> selectors = new ArrayList<>();
        List<ProofFormula> toCheck;
        if(polarity == TermSelector.SequentPolarity.ANTECEDENT){
            toCheck = seq.getAntecedent();
        } else {
            toCheck = seq.getSuccedent();
        }
        for(int i = 0; i < toCheck.size(); i++){
            ProofFormula f = toCheck.get(i);
            if(formulas.contains(f)){
                selectors.add(new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, i));
            }
        }
        return selectors;

    }

    private Term computeTermValue(ProofTermReferenceTarget target, Proof proof){
        return computeTermValue(target.getProofNodeSelector(), target.getTermSelector(), proof);
    }
    /**
     * Helper to select terms in a sequent acc. to given selectors
     * @param proofNodeSelector
     * @param termSelector
     * @param proof
     * @return
     */
    private Term computeTermValue(ProofNodeSelector proofNodeSelector, TermSelector termSelector, Proof proof) {
        Term ret = null;
        try {
            ret = termSelector.selectSubterm(proofNodeSelector.get(proof).getSequent());
            return ret;
        } catch (RuleException e) {
            return null;
        }

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
