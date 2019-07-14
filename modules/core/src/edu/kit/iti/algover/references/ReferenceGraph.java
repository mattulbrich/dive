/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
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
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import org.antlr.runtime.Token;

import java.io.File;
import java.util.*;
import java.util.function.Function;
import java.util.logging.Logger;
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

            //TODO letexpansion abfangen und Sonderbehandlung
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

    /**
     * Add all references from a scriptASTNode to ProofTermReferenceTargets
     * @param node Script ASTNode which transcribes a rule application
     * @param pNode The proof node to which the proof rule was applied
     */
    public void addFromScriptNode(ASTNode node, ProofNode pNode, Proof proof) throws RuleException {
        ScriptReferenceTarget sct = new ScriptReferenceTarget(pNode.getPVC(), node.getStartPosition().getLineNumber(), node);
        ScriptReferenceBuilder srb = new ScriptReferenceBuilder(this, sct, pNode, proof);
        srb.buildReferences(pNode.getChildren());
        this.getGraph();

    }


    /**
     * Compute direct parents of type ProofTermReferenceTarget transitively starting at childTarget and ending in the
     * root ProofNode. This method also returns all unchanged parents.
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
        toCompute.addAll(parents);
        while (toCompute.size() > 0) {
            Set<ProofTermReferenceTarget> directParents = findDirectParents(currentTarget, proof);
            toCompute.addAll(directParents);
            parents.addAll(directParents);
            currentTarget = toCompute.pop();
        }

        return parents;
    }

    /**
     * Comput the History of a proof Term reference target and return a sorted list of decendents starting with the root
     * @param childTarget
     * @param proof
     * @return
     */
    public List<ProofTermReferenceTarget> computeHistorySorted(ProofTermReferenceTarget childTarget, Proof proof){
        Set<ProofTermReferenceTarget> proofTermReferenceTargets = computeHistory(childTarget, proof);
        return proofTermReferenceTargets.stream().sorted(new ProofTermReferenceTargetComparator()).collect(Collectors.toList());
    }

    /**
     * Find the direct parent of childTarget in the reference graph, i.e, the term at the same position in the parent node or
     * the parent term if it has changed
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
                parents = computeDirectParents(currentTarget, proof);
            } else {
                //We have a predecessor in the graph
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

        if (termOfCurrenTarget == termOfParentTarget && termOfCurrenTarget != null) {
            parents.add(parent);
        } else {//termvalues are different
            ProofNode proofNode = currentTarget.getProofNodeSelector().get(proof);
            TermSelector childSelector = currentTarget.getTermSelector();
            ImmutableList<BranchInfo> branchInfos = proofNode.getProofRuleApplication().getBranchInfo();
            //filter branchinfos

            BranchInfo deltaToCurrentTarget;
            if(branchInfos.size() > 1){
                //filter the branchinfo for the child acc. to label
                Collection<BranchInfo> filteredBranchInfos = branchInfos.filter(
                        branchInfo -> branchInfo.getLabel().equals(proofNode.getLabel())).asCollection();
                assert filteredBranchInfos.size() == 1;
                deltaToCurrentTarget = filteredBranchInfos.iterator().next();
            } else {
                deltaToCurrentTarget = branchInfos.get(0);
            }


            if (!childSelector.isToplevel()) {
                //get all changes and check termselectors
                branchInfos.forEach(branchInfo -> {
                            branchInfo.getReplacements().forEach(termSelectorTermPair -> {
                                if (childSelector.hasPrefix(termSelectorTermPair.getFst())) {
                                    //TODO richtig umsetzen, bisher Überapprox.
                                    Term changedTerm = computeTermValue(currentTarget.getProofNodeSelector().getParentSelector(), termSelectorTermPair.getFst(), proof);
                                    if(changedTerm instanceof LetTerm){
                                       TermSelector parentSel = termSelectorTermPair.getFst();
                                        for(int i = 0; i < changedTerm.getSubterms().size(); i++){
                                                parents.add(new ProofTermReferenceTarget(currentTarget.getProofNodeSelector().getParentSelector(), new TermSelector(parentSel, i)));
                                        }
                                    } else {
                                        parents.add(new ProofTermReferenceTarget(currentTarget.getProofNodeSelector().getParentSelector(), termSelectorTermPair.getFst()));
                                    }
                                }
                            });
                        }

                );


                ProofTermReferenceTarget parentsInOffset = findParentsInOffset(proof, parent, currentTarget, childSelector, deltaToCurrentTarget);
                if(parentsInOffset != null) {
                    parents.add(parentsInOffset);
                }
            //    parents.add(handleAddAndDel(proof, parent, childSelector, branchInfos));

            } else {
                ProofTermReferenceTarget parentsInOffset = findParentsInOffset(proof, parent, currentTarget, childSelector, deltaToCurrentTarget);
                if(parentsInOffset != null) {
                    parents.add(parentsInOffset);
                }
              //  parents.add(handleAddAndDel(proof, parent, childSelector, branchInfos));
            }

        }
        return parents;
    }

    private ProofTermReferenceTarget findParentsInOffset(Proof proof, ProofTermReferenceTarget parent,
                                                         ProofTermReferenceTarget child,
                                      TermSelector childSelector,
                                      BranchInfo branchInfo) throws RuleException {

        Sequent additions = branchInfo.getAdditions();
        Sequent deletions = branchInfo.getDeletions();

        //check whether formula might have just moved position
        Sequent parentSeq = parent.getProofNodeSelector().get(proof).getSequent();

        List<TermSelector> deletedSelectors;
        if(childSelector.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT){
           deletedSelectors = computeSelector(deletions.getAntecedent(), parentSeq, childSelector.getPolarity());

        } else {
            deletedSelectors = computeSelector(deletions.getSuccedent(), parentSeq, childSelector.getPolarity());
        }
        List<TermSelector> greaterOrEqualTotarget = new ArrayList<>();
        deletedSelectors.forEach(termSelector -> {
            if(termSelector.getToplevelSelector().getTermNo() <= childSelector.getToplevelSelector().getTermNo()){
                greaterOrEqualTotarget.add(termSelector);
            }
        });

        TermSelector childWithOffset = new TermSelector(childSelector.getPolarity(),
                childSelector.getTermNo()+greaterOrEqualTotarget.size(),
                childSelector.getSubtermSelector());

        if(childWithOffset.isValidForSequent(parentSeq)) {
            Term term = childWithOffset.selectSubterm(parentSeq);

            if (term == childSelector.selectSubterm(child.getProofNodeSelector().get(proof).getSequent())) {
                return new ProofTermReferenceTarget(parent.getProofNodeSelector(), childWithOffset);
            }
        }

        //we checked whether formula may have just moved because of a deletion
        //as we still did not find the formula, we have to see, whether it was added by a rule app
        List<TermSelector> addedSelectors;
        if(childSelector.getPolarity() == TermSelector.SequentPolarity.ANTECEDENT){
            addedSelectors = computeSelector(additions.getAntecedent(), parentSeq, childSelector.getPolarity());

        } else {
            addedSelectors = computeSelector(additions.getSuccedent(), parentSeq, childSelector.getPolarity());
        }
        List<TermSelector> samePrefix = new ArrayList<>();
        addedSelectors.forEach(termSelector -> {
            if(childSelector.hasPrefix(termSelector)){
                samePrefix.add(termSelector);
            }
        });
        samePrefix.forEach(termSelector -> {
            try {
                Term x = termSelector.selectSubterm(child.getProofNodeSelector().get(proof).getSequent());
                System.out.println(x);
            } catch (RuleException e) {
                e.printStackTrace();
            }
        });
        //if not found in add or delete we search the parent for the formula as last resort
        return null;
    }

    /**
     * Return the ProofTermReferenceTarget in which a change to the target was made by a rule application. If no change
     * occurred to the target, the root of the proof is returned
     * @param proof
     * @param target
     * @return
     */
    public ProofTermReferenceTarget computeFirstParentWithChangedTerm(Proof proof, ProofTermReferenceTarget target){
        Set<ProofTermReferenceTarget> history = computeHistory(target, proof);
        ArrayList<ProofTermReferenceTarget> historyList = new ArrayList<>();
        historyList.addAll(history);
        historyList.sort(new ProofTermReferenceTargetComparator());
        TermSelector lastSelector = historyList.get(0).getTermSelector();
        for(ProofTermReferenceTarget p : historyList){
            if(!p.getTermSelector().equals(lastSelector)){
                return p;
            }
        }
        return historyList.get(historyList.size()-1);
    }

    public ProofTermReferenceTarget computeTargetBeforeChange(Proof proof, ProofTermReferenceTarget target) throws RuleException {
        if(target.getProofNodeSelector().getParentSelector() != null) {
            Set<ProofTermReferenceTarget> history = computeHistory(target, proof);
            ArrayList<ProofTermReferenceTarget> historyList = new ArrayList<>();
            historyList.addAll(history);
            historyList.sort(new ProofTermReferenceTargetComparator());
            TermSelector lastSelector = historyList.get(0).getTermSelector();
            ProofTermReferenceTarget current;
            ProofTermReferenceTarget before = historyList.get(0);

            Iterator<ProofTermReferenceTarget> iterator = historyList.iterator();
            while (iterator.hasNext()) {
                current = iterator.next();
                Term termCurrent = current.getTermSelector().selectSubterm(current.getProofNodeSelector().get(proof).getSequent());
                Term beforeTerm = before.getTermSelector().selectSubterm(before.getProofNodeSelector().get(proof).getSequent());
                if (!current.getTermSelector().equals(lastSelector) || !termCurrent.equals(beforeTerm)) {
                    return before;
                }
                before = current;

            }
            return historyList.get(historyList.size() - 1);
        } else {
            return target;
        }

    }

    //TODO refactor and possible additions
    //Currently its a naive implementation
    private ProofTermReferenceTarget handleAddAndDel(Proof proof, ProofTermReferenceTarget parent,
                                                     TermSelector childSelector,
                                                     ImmutableList<BranchInfo> branchInfos) throws RuleException {
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
            boolean containsF = false;
            Iterator<ProofFormula> iterator = formulas.iterator();

            while(!containsF && iterator.hasNext()){
                ProofFormula next = iterator.next();
                containsF = (next.getTerm() == f.getTerm());
            }

            if(containsF){
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

    private static class ProofTermReferenceTargetComparator implements Comparator<ProofTermReferenceTarget> {
        @Override
        public int compare(ProofTermReferenceTarget o1, ProofTermReferenceTarget o2) {

            if(o1.getProofNodeSelector().getPath().length > o2.getProofNodeSelector().getPath().length){
                return -1;
            } else {
                return 1;
            }
        }
    }
}
