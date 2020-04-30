package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.references.ScriptReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.HistoryProofUtils;
import edu.kit.iti.algover.util.ProofUtils;
import edu.kit.iti.algover.util.TestInfrastructure;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.util.logging.Logger;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphDirectParentsInProofsTest {

    private Proof proofWithTwoSubstitutionsAndSkips;

    private Proof proofBranched;

    private Proof proofWithRemoval;

    private Proof proofWithReplacement;

    private Object[][] unchangedFormulas() {
        return new Object[][]
                {
                        new Object[]{"0,0", "A.0"},
                        new Object[]{"0,0", "A.0.0"},
                        new Object[]{"0,0", "A.0.0.0"},
                        new Object[]{"0,0", "A.0.0.1"},
                        new Object[]{"0", "S.0"},
                        new Object[]{"0", "S.0.0"},
                        new Object[]{"0", "S.0.1"},
                };
    }

    private Object[][] changedFormulas(){
        return new Object[][]
                {

                        new Object[]{"0", "A.0.0"}, //Dieser Fall muss noch besser behandelt werden -> innerhalb einer Ersetzung: hier stimmen weder position noch Term
                        new Object[]{"0", "A.0"},
                        new Object[]{"0", "A.0.0.1"},
                        new Object[]{"0", "A.0.0.0"},
                        new Object[]{"0,0", "S.0"},
                        new Object[]{"0,0", "S.0.1"},
                        new Object[]{"0,0", "S.0.0"},

                };

    }

    /**
     * Proof:
     * Root: (let m := x :: $not($lt(m, y))) |- (let m := x :: $gt(m, 1))
     * Rule: substitute on='... ((?match: let m := x :: !(m < y))) ... |-';
     * 0: $not($lt(x, y)) |- (let m := x :: $gt(m, 1))
     * Rule: substitute on='|- ... ((?match: let m := x :: m > 1)) ...';
     * 0.0: $not($lt(x, y)) |- $gt(x, 1)
     */

    @Before
    public void testProjectLoad() throws Exception {

        XMLProjectManager pm = null;
            URL resource = getClass().getResource("./referenceGraphTest");

            pm = new XMLProjectManager(new File(resource.getFile()), "config.xml");
            pm.reload();
            proofWithTwoSubstitutionsAndSkips = pm.getProofForPVC("max/else/Post");
            proofWithTwoSubstitutionsAndSkips.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                    "substitute on='|- ... ((?match: let m := x :: m > 1)) ...';\n"+"skip;\n"+"skip;\n");

            if(proofWithTwoSubstitutionsAndSkips.getFailException() != null) {
                proofWithTwoSubstitutionsAndSkips.getFailException().printStackTrace();
            }
            assertEquals(ProofStatus.OPEN, proofWithTwoSubstitutionsAndSkips.getProofStatus());

            proofBranched = pm.getProofForPVC("max/then/Post.1");
            String script2 = "substitute on='... ((?match: let m := x :: m < y)) ... |-';\n" +
                    "skip;\n" +
                    "substitute on='|- ... ((?match: let m := y :: m >= x && m >= y)) ...';\n" +
                    "skip;\n" +
                    "andRight on='|- ... ((?match: y >= x && y >= y)) ...';\n" +
                    "cases {\n" +
                    "\tcase match \"case 1\": {\n" +
                    "\t\n" +
                    "skip;\n" +
                    "\t}\n" +
                    "\tcase match \"case 2\": {\n" +
                    "\t\n" +
                    "skip;\n" +
                    "\t}\n" +
                    "}";
            proofBranched.setScriptTextAndInterpret(script2);
            if(proofBranched.getFailException() != null) {
                proofBranched.getFailException().printStackTrace();
            }
            assertEquals(ProofStatus.OPEN, proofBranched.getProofStatus());



            //has addlist+delList
            proofWithRemoval = pm.getProofForPVC("ff/Post");
            proofWithRemoval.setScriptTextAndInterpret("andLeft on='... ((?match: a >= 0 && a < 100)) ... |-';\n"+
                    "removeAssumption on='... ((?match: a + 1 == a + 1 && a > 0 ==> b >= 0)) ... |-';\n");


            String script = "substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                    "replace with='x == y' on='... ((?match: !(x < y))) ... |-';\n" +
                    "cases {\n" +
                    "\tcase match \"replace\": {\n" +
                    "\t\n" +
                    "\t}\n" +
                    "\tcase match \"justification\": {\n" +
                    "\t\n" +
                    "\t}\n" +
                    "}\n" +
                    "\n";

            proofWithReplacement = pm.getProofForPVC("max/else/Post.1");
            proofWithReplacement.setScriptTextAndInterpret(script);
            if(proofWithReplacement.getFailException() != null) {
                proofWithReplacement.getFailException().printStackTrace();
            }
            assertEquals(ProofStatus.OPEN, proofWithReplacement.getProofStatus());

    }

    /**
     * This test tests whether all terms and subterms in a sequent are unchanged after the application of the skip rule
     * @throws RuleException
     * @throws FormatException
     */
    @Test
    public void testSkipRule() throws RuleException, FormatException {

        ProofNodeSelector lastNode = ProofUtils.computeProofNodeSelector("0,0,0,0");
        Sequent lastSeq = lastNode.get(proofWithTwoSubstitutionsAndSkips).getSequent();
        List<TermSelector> allSelectors = ProofUtils.computeAllSelectors(lastSeq);
        allSelectors.forEach(termSelector -> {
            Assert.assertTrue(isFormulaUnchangedInDirectParent("0,0,0,0", termSelector.toString(), proofWithTwoSubstitutionsAndSkips));
        });
        ProofNodeSelector lastNodeBefore = ProofUtils.computeProofNodeSelector("0,0,0");
        Sequent lastSeqBefore = lastNodeBefore.get(proofWithTwoSubstitutionsAndSkips).getSequent();
        List<TermSelector> allSelectorsBefore = ProofUtils.computeAllSelectors(lastSeqBefore);
        allSelectorsBefore.forEach(termSelector -> {
            Assert.assertTrue(isFormulaUnchangedInDirectParent("0,0,0", termSelector.toString(), proofWithTwoSubstitutionsAndSkips));
        });


    }

    @Test
    public void testScriptReferences() throws RuleException, FormatException {
        ProofNodeSelector replaceNode = ProofUtils.computeProofNodeSelector("0,0,0,0,0");
        Sequent replace = replaceNode.get(proofBranched).getSequent();
        ProofNodeSelector justNode = ProofUtils.computeProofNodeSelector("0,0,0,0,1,0");
        Sequent just = justNode.get(proofBranched).getSequent();
        TermSelector ltFormula = new TermSelector("A.0");
        TermSelector x = new TermSelector("A.0.0");
        TermSelector y = new TermSelector("A.0.1");
        TermSelector sx = new TermSelector("S.0.1");
        TermSelector sy = new TermSelector("S.0.0");
        TermSelector geFormula = new TermSelector("S.0");


        ProofTermReferenceTarget childTarget = new ProofTermReferenceTarget(justNode, sy);
        ReferenceGraph graph = proofBranched.getGraph();
        ProofTermReferenceTarget proofTermReferenceTarget = graph.computeTargetBeforeChange(proofBranched, childTarget);


        System.out.println("proofTermReferenceTarget1 = " + proofTermReferenceTarget);
        Set<ScriptReferenceTarget> scriptReferenceTargetSet = graph.allSuccessorsWithType(proofTermReferenceTarget, ScriptReferenceTarget.class);
        scriptReferenceTargetSet.forEach(scriptReferenceTarget -> System.out.println("scriptReferenceTarget = " + scriptReferenceTarget));


        // Set<ScriptReferenceTarget> scriptReferenceTargetSet = proofBranched.getGraph().allSuccessorsWithType(childTarget, ScriptReferenceTarget.class);
       // scriptReferenceTargetSet.forEach(scriptReferenceTarget -> System.out.println("scriptReferenceTarget = " + scriptReferenceTarget));

    }


    /**
     * Test parents of formulas that have been part of a replacement
     */
    @Test
    public void testReplacements() throws RuleException, FormatException {
        //proofWithReplacement;
        Assert.assertFalse(isFormulaUnchangedInDirectParent("0,0", "A.0", proofWithReplacement));
        //SaG: atm the parent whole replaced formula is returned, therefore although term value is still part of whole formula it is considered as changed
        Assert.assertFalse(isFormulaUnchangedInDirectParent("0,0", "A.0.1", proofWithReplacement));
        Assert.assertFalse(isFormulaUnchangedInDirectParent("0,0", "A.0.0", proofWithReplacement));
        Set<ProofTermReferenceTarget> parentsReplace = computeDirectParents("0,0", "A.0.1", proofWithReplacement);
        Assert.assertTrue(parentsReplace.size() == 1);
        Assert.assertEquals(parentsReplace.iterator().next().getTermSelector().toString(),"A.0");

        Set<ProofTermReferenceTarget> parentsJust = computeDirectParents("0,0", "A.0.0", proofWithReplacement);
        Assert.assertTrue(parentsJust.size() == 1);
        Assert.assertEquals(parentsJust.iterator().next().getTermSelector().toString(),"A.0");
    }



    /**
     * Test formulas that have been affected by additions or deletions
     * @throws FormatException
     * @throws RuleException
     */
    @Test
    public void testDelList() throws FormatException, RuleException {
        ProofNodeSelector pns = ProofUtils.computeProofNodeSelector("0,0");
        TermSelector termSelector = new TermSelector("A.1");
        //sequent: $ge(a, 0), $lt(a, 100) |- $and($eq<int>(a, 1), $eq<int>($$f($heap, $$f($heap, a)), 2))
        //selection: $lt(a, 100)
        //parent should be: A.2 in
        //parentSeq:$ge(a, 0), $imp($and($eq<int>($plus(a, 1), $plus(a, 1)), $gt(a, 0)), $ge(b, 0)), $lt(a, 100)
        // |- $and($eq<int>(a, 1), $eq<int>($$f($heap, $$f($heap, a)), 2))
        Sequent sequent = pns.get(proofWithRemoval).getSequent();
        System.out.println("sequent = " + sequent);

        Set<ProofTermReferenceTarget> parents = computeDirectParents("0,0", "A.1", proofWithRemoval);
        Term proofFormula = termSelector.selectSubterm(sequent);

        parents.forEach(parent -> {
            try {
                boolean comp = HistoryProofUtils.compareTerms(proofFormula, parent, proofWithRemoval);
                Logger.getGlobal().info("comp = " + comp);
            } catch (RuleException e) {
                e.printStackTrace();
            }
        });
    }

    public boolean testMethodForWithtwoSubstAndSkips(String path, String termSelector){
         return isFormulaUnchangedInDirectParent(path, termSelector, proofWithTwoSubstitutionsAndSkips);
    }

    public boolean testMethodForProofBranched(String path, String termSelector){
        return isFormulaUnchangedInDirectParent(path, termSelector, proofBranched);
    }


    @Test
    @Parameters(method="unchangedFormulas")
    public void testIfFormulaUnchangedInDirectParent(String a, String b){
        Assert.assertEquals(testMethodForWithtwoSubstAndSkips(a,b), true);
    }

    @Test
    @Parameters(method="changedFormulas")
    public void testIfFormulaChangedInDirectParent(String a, String b){
        Assert.assertEquals(testMethodForWithtwoSubstAndSkips(a,b), false);
    }


    private Set<ProofTermReferenceTarget> computeDirectParents(String pathChild, String termSelectorString, Proof currentProof) throws FormatException {
        ProofNodeSelector pns = ProofUtils.computeProofNodeSelector(pathChild);
        TermSelector termSelector = new TermSelector(termSelectorString);
        Set<ProofTermReferenceTarget> directParents = currentProof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), currentProof);
        return directParents;
    }


       /**
     * False iff term or formula changed from pathChild to direct parent, true iff term or formula unchanged
     * @param pathChild
     * @param termSelectorString
     * @param currentProof
     * @return
     */
    private boolean isFormulaUnchangedInDirectParent(String pathChild, String termSelectorString, Proof currentProof){

        boolean ret = false;
        ProofNodeSelector pns = ProofUtils.computeProofNodeSelector(pathChild);

        try {
            TermSelector termSelector = new TermSelector(termSelectorString);
            Set<ProofTermReferenceTarget> directParents = currentProof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), currentProof);
            Term proofFormula = termSelector.selectSubterm(pns.get(currentProof).getSequent());
            Logger.getGlobal().info("Test for proof node " + pns + " term " + proofFormula);

            for (ProofTermReferenceTarget directParent : directParents) {
                Term term = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(currentProof).getSequent());
                if(ret = term == proofFormula){
                    Logger.getGlobal().info("Term value " + term + " has not changed from node "+pns.getParentSelector()+" to "+pns);
                    if(directParent.getTermSelector() != termSelector){
                        Logger.getGlobal().info("But position has changed");
                        ret = false;
                    } else {
                        Logger.getGlobal().info("and position has not changed");
                    }

                } else {

                    Logger.getGlobal().info("term = " + term+ " and "+proofFormula+ " are not identical");
                }
            }
        } catch (FormatException e) {
            e.printStackTrace();
        } catch (RuleException e) {
            e.printStackTrace();
        }
        return ret;

    }






}
