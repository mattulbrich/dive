/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;


import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Methods to apply a ProofRuleAppplication to a ProofNode.
 *
 * @author Sarah Grebing
 */
public final class RuleApplicator {

    private RuleApplicator() {
        throw new Error("not to be instantiated");
    }

    /**
     * Apply a Proof Rule to a proof node.
     *
     * @param app the proof rule application to be applied
     * @param command
     * @param pn                   the ProofNode to which the rule should be applied
     * @return a list of new proof nodes (children) resulting form the rule application
     */
    public static List<ProofNode> applyRule(ProofRuleApplication app, Command command, ProofNode pn) throws TermBuildException {

        List<ProofNode> newNodes = applySingleApplication(app, command, pn);
        ImmutableList<ProofRuleApplication> subApps = app.getSubApplications();
        if(subApps != null) {
            assert subApps.size() == newNodes.size();
            for (int i = 0; i < newNodes.size(); ++i) {
                if (subApps.get(i) != null) {
                    newNodes.get(i).setChildren(applyRule(subApps.get(i), command, newNodes.get(i)));
                }
            }
        }
        return newNodes;
    }

    private static List<ProofNode> applySingleApplication(ProofRuleApplication appl, Command command, ProofNode proofNode) throws TermBuildException {

        ImmutableList<BranchInfo> infos = appl.getBranchInfo();

        if (infos.equals(BranchInfo.CLOSE)) {
            // for a closing rule application add an artificial node that manifests the application.
            ProofNode markerNode = ProofNode.createClosureChild(proofNode, appl,  command);
            markerNode.setChildren(Collections.emptyList());
            return List.of(markerNode);
        }

        Sequent sequent = proofNode.getSequent();

        List<ProofNode> result = new ArrayList<>();

        for (BranchInfo branchInfo : infos) {
            Sequent newSequent = null;
            newSequent = createNewSequent(branchInfo, sequent);
            ProofNode pnNew = ProofNode.createChild(proofNode, appl,
                    branchInfo.getLabel(), command, newSequent);
            appl.getNewFunctionSymbols().forEach(
                    functionSymbol -> pnNew.getAddedSymbols().addFunctionSymbol(functionSymbol));
            result.add(pnNew);

        };

        return result;
    }

    /**
     * Create a new Sequent by using the branchinfo to change the old sequent
     *
     * @param branchInfo information how the old sequent should be changed to get teh new sequent
     * @param oldSeq     old sequent to which the changes should be applied to
     * @return a new created sequent considering the branchinfo
     * @throws TermBuildException
     */
    private static Sequent createNewSequent(BranchInfo branchInfo, Sequent oldSeq) throws TermBuildException {
        Sequent additions = branchInfo.getAdditions();
        Sequent deletions = branchInfo.getDeletions();

        Iterable<Pair<TermSelector, Term>> replacements = branchInfo.getReplacements();
        List<Pair<TermSelector, Term>> antecReplacements = new ArrayList<>();
        List<Pair<TermSelector, Term>> succReplacements = new ArrayList<>();
        replacements.forEach(termSelectorTermPair -> {
            if (termSelectorTermPair.getFst().isAntecedent()) {
                antecReplacements.add(termSelectorTermPair);
            } else {
                succReplacements.add(termSelectorTermPair);
            }
        });

        List<ProofFormula> antec = changeSemisequent(additions.getAntecedent(),
                deletions.getAntecedent(), antecReplacements, oldSeq.getAntecedent());

        List<ProofFormula> succ = changeSemisequent(additions.getSuccedent(),
                deletions.getSuccedent(), succReplacements, oldSeq.getSuccedent());

        Util.removeDuplicates(antec);
        Util.removeDuplicates(succ);

        Sequent newSeq = new Sequent(antec, succ);
        return newSeq;
    }

    /**
     * Change a semisequent according to the infos from the rule application
     *
     * IMPORTANT: exhaustive rule application expects the following behaviour when changing the sequent:
     *      - additions are always made at the end (so they dont effect termselectors)
     *      - replacements are always applied in a way that the replacements are in the same position as the original
     *      terms
     *
     * @param add        formulas to add to the old sequent
     * @param delete     formulas to delete from the old sequent
     * @param change     formulas that have to be changed
     * @param oldSemiSeq teh old sequent which needs to be changed
     * @return a new Sequent that considers the change information
     * @throws TermBuildException
     */
    private static List<ProofFormula> changeSemisequent(List<ProofFormula> add,
            List<ProofFormula> delete, List<Pair<TermSelector, Term>> change,
            List<ProofFormula> oldSemiSeq) throws TermBuildException {
        List<ProofFormula> newSemiSeq = new ArrayList<>(oldSemiSeq);
        for (Pair<TermSelector, Term> termSelectorTermPair : change) {
            Term newTerm = termSelectorTermPair.snd;
            TermSelector ts = termSelectorTermPair.fst;
            ProofFormula nthForm = oldSemiSeq.get(ts.getTermNo());
            Term replace = ReplaceVisitor.replace(nthForm.getTerm(), ts.getSubtermSelector(), newTerm);
            newSemiSeq.set(ts.getTermNo(), new ProofFormula(replace, nthForm.getLabels()));
        }

        for(ProofFormula pf : delete) {
            for(int i = newSemiSeq.size() - 1; i >= 0; --i) {
                ProofFormula f = newSemiSeq.get(i);
                if(f.getTerm().equals(pf.getTerm())) {
                    newSemiSeq.remove(f);
                }
            }
        }
        newSemiSeq.addAll(add);

        return newSemiSeq;
    }
}
