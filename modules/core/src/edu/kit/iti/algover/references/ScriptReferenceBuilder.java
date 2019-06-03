package edu.kit.iti.algover.references;


import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

import java.util.*;


/**
 * Creates references between ScriptNodes and Terms. A term is part of a reference \<Script, Term\> iff
 * it was either added or replaced by the rule command that is encoded in the
 * ScriptNode
 */
public class ScriptReferenceBuilder {

    private final ScriptReferenceTarget sct;

    private final ProofNodeSelector parentSelector;

    private final Proof proof;

    private final ReferenceGraph graph;

    public ScriptReferenceBuilder(ReferenceGraph referenceGraph, ScriptReferenceTarget sct, ProofNode pNode, Proof proof) {
        this.sct = sct;
        this.parentSelector = new ProofNodeSelector(pNode);
        this.proof = proof;
        this.graph = referenceGraph;

    }


    public void buildReferences(List<ProofNode> children) throws RuleException {
        for (ProofNode afterNode : children) {
            //get ProofRuleApplication from node
            ProofNodeSelector pns = new ProofNodeSelector(afterNode);
            ProofRuleApplication pra = afterNode.getProofRuleApplication();


            ImmutableList<BranchInfo> branchInfos = pra.getBranchInfo();
            for (BranchInfo bi : branchInfos) {
                //handle replacements
                ImmutableList<Pair<TermSelector, Term>> replacements = bi.getReplacements();
                for (Pair<TermSelector, Term> repl : replacements) {
                    this.buildReferencesForTerm(pns, repl.getFst());
                }

                Sequent additions = bi.getAdditions();
                //todo add references for each term and subterm  in additions
                List<ProofFormula> antecedent = additions.getAntecedent();
                List<ProofFormula> antecedentInNode= afterNode.getSequent().getAntecedent();
                for (ProofFormula toplevel: antecedent) {
                    //TermSelektoren für jeden Toplevel Term in Sequent finden
                    TermSelector sel = findSelector(toplevel, antecedentInNode, TermSelector.SequentPolarity.ANTECEDENT);
                    //Referenz für jeden Subterm hinzufügen
                    if(sel != null)
                        buildReferencesForTerm(pns, sel);
                }
                List<ProofFormula> succedent = additions.getSuccedent();
                //Sequent deletions = bi.getDeletions();
                List<ProofFormula> succedentInNode= afterNode.getSequent().getSuccedent();
                for (ProofFormula toplevel: succedent) {
                    //TermSelektoren für jeden Toplevel Term in Sequent finden
                    TermSelector sel = findSelector(toplevel, succedentInNode, TermSelector.SequentPolarity.SUCCEDENT);
                    //Referenz für jeden Subterm hinzufügen
                    if(sel != null)
                        buildReferencesForTerm(pns, sel);
                }

            }

        }

    }

    /**
     * Searches for the prooformula in the cedent and returns its termselector. If the prooformula
     * does not exist, this method throws an exception.
     *
     * @param formula
     * @param cedent
     * @return Termselector of formula in cedent
     */
    private TermSelector findSelector(ProofFormula formula, List<ProofFormula> cedent, TermSelector.SequentPolarity polarity) throws NoSuchElementException{
        int index = 0;
        boolean found = false;
        Iterator<ProofFormula> iterator = cedent.iterator();
        ProofFormula currentFormula;

        //find first occurrence
        while(iterator.hasNext()){
            currentFormula = iterator.next();
            if(currentFormula.equals(formula)){
                found = true;
               break;
            }
            index++;
        }

        if(found){
            return  new TermSelector(polarity, index);
        } else {
            return null;
            //throw  new NoSuchElementException("The formula could not be found in the cedent while searching for references");
        }

    }
    private void buildReferencesForTerm(ProofNodeSelector proofNodeAfter, TermSelector changedTerm) throws RuleException {
        ProofTermReferenceTarget pt = new ProofTermReferenceTarget(proofNodeAfter, changedTerm);
        graph.addReference(pt, sct);
        Sequent sequent = proofNodeAfter.get(proof).getSequent();
        TermCollector collector = new TermCollector();
        collector.collectInSequent(sequent, changedTerm);
        Map<TermSelector, Term> collectedTerms = collector.getCollectedTerms();
        Set<TermSelector> termSelectors = collectedTerms.keySet();

        for (TermSelector ts : termSelectors) {
            ProofTermReferenceTarget target = new ProofTermReferenceTarget(proofNodeAfter, ts);
            graph.addReference(target, sct);
        }
    }
}
