package edu.kit.iti.algover.rules;


import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;


import java.util.ArrayList;
import java.util.List;

/**
 * Methods to apply a ProofRuleAppplication to a ProofNode
 */
public class RuleApplicator {

    /**
     * Apply a Proof Rule to a proof node
     *
     * @param proofRuleApplication the proof rule application to be applied
     * @param pn                   the ProofNode to which the rule should be applied
     * @return a list of new proof nodes (children) resulting form the rule application
     */
    public static List<ProofNode> applyRule(ProofRuleApplication proofRuleApplication, ProofNode pn) {

        List<ProofNode> newNodes = applySingleApplication(proofRuleApplication, pn);
        ImmutableList<ProofRuleApplication> subApps = proofRuleApplication.getSubApplications();
        if(subApps != null) {
            assert(subApps.size() == newNodes.size());
            for (int i = 0; i < newNodes.size(); ++i) {
                if (subApps.get(i) != null) {
                    newNodes.get(i).setChildren(applyRule(subApps.get(i), newNodes.get(i)));
                }
            }
        }
        return newNodes;
    }

    private static List<ProofNode> applySingleApplication(ProofRuleApplication proofRuleApplication, ProofNode pn) {

        ImmutableList<BranchInfo> applicationInfos = proofRuleApplication.getBranchInfo();
        if (applicationInfos.equals(BranchInfo.UNCHANGED)) {
            ProofNode unchanged = new ProofNode(pn, proofRuleApplication, pn.getSequent(), pn.getPVC());
            //pn.getChildren().add(unchanged);
            List<ProofNode> retList = new ArrayList<>();
            retList.add(unchanged);
            return retList;
        }
        if (applicationInfos.equals(BranchInfo.CLOSE)) {
            //TODO handle closed case
        }
        Sequent sequent = pn.getSequent();

        int numberOfChildrenExpected = applicationInfos.size();

        List<ProofNode> children = new ArrayList<>();

        applicationInfos.forEach(branchInfo -> {
            Sequent newSequent = null;
            try {
                newSequent = createNewSequent(branchInfo, sequent);
                ProofNode pnNew = new ProofNode(pn, proofRuleApplication, newSequent, pn.getPVC());
                proofRuleApplication.getNewFunctionSymbols().forEach(
                        functionSymbol -> pnNew.getAddedSymbols().addFunctionSymbol(functionSymbol));
                pnNew.setLabel(branchInfo.getLabel());
                children.add(pnNew);

            } catch (TermBuildException e) {
                e.printStackTrace();
            }

        });
        assert numberOfChildrenExpected == children.size();


        return children;
    }

    /**
     * Create a new Sequent by using the branchinfo to change the old sequent
     *
     * @param branchInfo information how the old sequent should be changed to get teh new sequent
     * @param oldSeq     old sequent to which the changes should be applied to
     * @return a new created sequent considering the branchinfo
     * @throws TermBuildException
     */

    protected static Sequent createNewSequent(BranchInfo branchInfo, Sequent oldSeq) throws TermBuildException {


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


        List<ProofFormula> antec = changeSemisequent(additions.getAntecedent(), deletions.getAntecedent(), antecReplacements, oldSeq
                .getAntecedent());
        List<ProofFormula> succ = changeSemisequent(additions.getSuccedent(), deletions.getSuccedent(), succReplacements, oldSeq
                .getSuccedent());


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
    protected static List<ProofFormula> changeSemisequent(List<ProofFormula> add, List<ProofFormula> delete, List<Pair<TermSelector, Term>> change, List<ProofFormula> oldSemiSeq) throws TermBuildException{
        List<ProofFormula> newSemiSeq = new ArrayList<>(oldSemiSeq);
        if (change.size() != 0) {
            change.forEach(termSelectorTermPair -> {
                Term newTerm = termSelectorTermPair.snd;
                TermSelector ts = termSelectorTermPair.fst;
                try {
                    ProofFormula nthForm = oldSemiSeq.get(ts.getTermNo());
                    Term replace = ReplaceVisitor.replace(nthForm.getTerm(), ts.getSubtermSelector(), newTerm);
                    newSemiSeq.set(ts.getTermNo(), new ProofFormula(replace));
                } catch (TermBuildException e) {
                    e.printStackTrace();
                }
            });
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
