package edu.kit.iti.algover.rules;


import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;


import javax.xml.soap.Node;
import java.util.ArrayList;
import java.util.Collections;
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
                children.add(pnNew);

            } catch (TermBuildException e) {
                e.printStackTrace();
            }

        });
        assert numberOfChildrenExpected == children.size();


        return children;
    }

    public static List<ProofNode> applyRuleExhaustive(ProofRuleApplication proofRuleApplication, ProofNode pn, TermSelector ts)  throws RuleException {
        List<ProofNode> nodes = applyRule(proofRuleApplication, pn);
        List<ProofNode> newNodes = new ArrayList<>(nodes);

        for (ProofNode node : nodes) {
            ProofRuleApplication newPra = new ProofRuleApplicationBuilder(proofRuleApplication.getRule())
                    .setApplicability(ProofRuleApplication.Applicability.NOT_APPLICABLE)
                    .build();
            if(ts.isValidForSequent(node.getSequent())) {
                newPra = proofRuleApplication.getRule().considerApplication(node, node.getSequent(), ts);
            }
            if (newPra.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
                newNodes.addAll(applyRuleExhaustive(newPra, node, ts));
                newNodes.remove(node);
            }
        }

        return newNodes;
    }

    private static TermSelector[] getAllChildSelectors(TermSelector ts, Sequent s) throws RuleException {
        Term selectedTerm;
        try {
            selectedTerm = ts.selectSubterm(s);
        } catch (RuleException e) {
            return new TermSelector[0];
        }
        int numSuberms = selectedTerm.getSubterms().size();
        TermSelector[] res = new TermSelector[numSuberms];
        for(int i = 0; i < numSuberms; ++i) {
            res[i] = new TermSelector(ts, i);
        }
        return res;
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
     * @param add        formauls to add to the oldsequent
     * @param delete     formulas to delet from the old sequent
     * @param change     fromulas that have to be changed
     * @param oldSemiSeq teh old sequent which needs to be changed
     * @return a new Sequent that considers tthe change information
     * @throws TermBuildException
     */
    protected static List<ProofFormula> changeSemisequent(List<ProofFormula> add, List<ProofFormula> delete, List<Pair<TermSelector, Term>> change, List<ProofFormula> oldSemiSeq) throws TermBuildException{
        List<ProofFormula> newSemiSeq = new ArrayList<>(add);
        List<Term> topLevels = new ArrayList<>();
        int i = 0;
        if (change.size() != 0) {
            change.forEach(termSelectorTermPair -> {
                Term newTerm = termSelectorTermPair.snd;
                TermSelector ts = termSelectorTermPair.fst;
                try {
                    ProofFormula nthForm = oldSemiSeq.get(ts.getTermNo());
                    topLevels.add(nthForm.getTerm());
                    Term replace = ReplaceVisitor.replace(nthForm.getTerm(), ts.getSubtermSelector(), newTerm);
                    nthForm = new ProofFormula(replace);
                    newSemiSeq.add(nthForm);

                } catch (TermBuildException e) {
                    e.printStackTrace();
                }
            });
        }

        delete.forEach(t -> topLevels.add(t.getTerm()));

        oldSemiSeq.forEach(proofFormula -> {
            if(!topLevels.contains(proofFormula.getTerm())){
                newSemiSeq.add(proofFormula);
            }
        });
        return newSemiSeq;
    }
}
