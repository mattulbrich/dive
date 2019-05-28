package edu.kit.iti.algover.references;


import edu.kit.iti.algover.proof.Proof;
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

import java.util.List;
import java.util.Map;
import java.util.Set;


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

                //TODO bi.getAdditions();

            }

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
