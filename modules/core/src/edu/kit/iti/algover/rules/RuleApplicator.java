package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;


import java.util.ArrayList;
import java.util.List;

/**
 * Methods to apply a ProofRuleAppplication to a ProofNode
 */
public class RuleApplicator {

    public static List<ProofNode> applyRule(ProofRuleApplication proofRuleApplication, ProofNode pn) {
        List<ProofNode> list = new ArrayList<>();
        ImmutableList<BranchInfo> applicationInfos = proofRuleApplication.getBranchInfo();
        if (applicationInfos.equals(BranchInfo.UNCHANGED)) {

            //TODO handle unchanged case
        }
        if (applicationInfos.equals(BranchInfo.CLOSE)) {
            //TODO handle closed case
        }
        Sequent sequent = pn.getSequent();
        int numberOfChildrenExpected = applicationInfos.size();
        List<ProofNode> children = new ArrayList<>();
        applicationInfos.forEach(branchInfo -> {
            System.out.println("branchInfo = " + branchInfo);
            Sequent newSequent = createNewSequent(branchInfo, sequent);
            ProofNode pnNew = new ProofNode(pn, proofRuleApplication, pn.getHistory(), newSequent, pn.getRootPVC());
            children.add(pnNew);
        });
        assert numberOfChildrenExpected == children.size();


        return list;
    }

    private static Sequent createNewSequent(BranchInfo branchInfo, Sequent oldSeq) {


        Sequent additions = branchInfo.getAdditions();
        Sequent deletions = branchInfo.getDeletions();
        Iterable<Pair<TermSelector, Term>> replacements = branchInfo.getReplacements();
        List<Pair<TermSelector, Term>> antecReplacements = new ArrayList<>();
        List<Pair<TermSelector, Term>> succReplacements = new ArrayList<>();
        replacements.forEach(termSelectorTermPair -> {
            if (termSelectorTermPair.getFst().equals(TermSelector.SequentPolarity.ANTECEDENT)) {
                antecReplacements.add(termSelectorTermPair);
            } else {
                succReplacements.add(termSelectorTermPair);
            }
        });


        List<ProofFormula> antec = changeSemisequent(additions.getAntecedent(), deletions.getAntecedent(), antecReplacements, oldSeq
                .getAntecedent());
        List<ProofFormula> succ = changeSemisequent(additions.getSuccedent(), deletions.getSuccedent(), succReplacements, oldSeq
                .getSuccedent());


        Sequent newSeq = new Sequent(antec, succ);
        return newSeq;

    }

    private static List<ProofFormula> changeSemisequent(List<ProofFormula> add, List<ProofFormula> delete, List<Pair<TermSelector, Term>> change, List<ProofFormula> oldSemiSeq) {
        List<ProofFormula> newSemiSeq = new ArrayList<>(add);
        oldSemiSeq.forEach(proofFormula -> {
            //check if formula in deletions
            if (!delete.contains(proofFormula)) {
                //check if formula in changes
                change.forEach(termSelectorTermPair -> {
                    //do replacements
                });
                newSemiSeq.add(proofFormula);
            }
        });

        return newSemiSeq;
    }
}
