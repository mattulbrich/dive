package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.references.ScriptReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.HistoryProofUtils;
import edu.kit.iti.algover.util.ProofUtils;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.Set;

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphDirectParentsSingleTests {
    private XMLProjectManager pm = null;

    @Before
    public void testProjectLoad(){


        try {
            URL resource = getClass().getResource("./referenceGraphTest");

            pm = new XMLProjectManager(new File(resource.getFile()), "config.xml");
            pm.reload();
           /* proofWithTwoSubstitutionsAndSkips = pm.getProofForPVC("max/else/Post");
            proofWithTwoSubstitutionsAndSkips.setScriptTextAndInterpret("substitute on='... ((?m: let m := x :: !(m < y))) ... |-';\n" +
                    "substitute on='|- ... ((?m: let m := x :: m > 1)) ...';\n"+"skip;\n"+"skip;\n");

            proofBranched = pm.getProofForPVC("max/then/Post.1");
            String script2 = "substitute on='... ((?m: let m := x :: m < y)) ... |-';\n" +
                    "skip;\n" +
                    "substitute on='|- ... ((?m: let m := y :: m >= x && m >= y)) ...';\n" +
                    "skip;\n" +
                    "andRight on='|- ... ((?m: y >= x && y >= y)) ...';\n" +
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

            //has addlist+delList
            proofWithRemoval = pm.getProofForPVC("ff/Post");
            proofWithRemoval.setScriptTextAndInterpret("andLeft on='... ((?m: a >= 0 && a < 100)) ... |-';\n"+
                    "removeAssumption on='... ((?m: a + 1 == a + 1 && a > 0 ==> b >= 0)) ... |-';\n");


            String script = "substitute on='... ((?m: let m := x :: !(m < y))) ... |-';\n" +
                    "replace with='x == y' on='... ((?m: !(x < y))) ... |-';\n" +
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
            proofWithReplacement.setScriptTextAndInterpret(script);*/

        } catch (FormatException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (DafnyParserException e) {
            e.printStackTrace();
        } catch (DafnyException e) {
            e.printStackTrace();
        }

    }

    /**
     * This test tests whether all terms and subterms in a sequent are unchanged after the application of the skip rule
     * @throws RuleException
     * @throws FormatException
     */
    @Test
    public void testSkipRule() throws RuleException, FormatException {
        Proof proofWithTwoSubstitutionsAndSkips = pm.getProofForPVC("max/else/Post");
        proofWithTwoSubstitutionsAndSkips.setScriptTextAndInterpret("substitute on='... ((?m: let m := x :: !(m < y))) ... |-';\n" +
                "substitute on='|- ... ((?m: let m := x :: m > 1)) ...';\n"+"skip;");

        ProofNodeSelector lastNode = ProofUtils.computeProofNodeSelector("0,0,0");
        Sequent lastSeq = lastNode.get(proofWithTwoSubstitutionsAndSkips).getSequent();
        List<TermSelector> allSelectors = ProofUtils.computeAllSelectors(lastSeq);
        for (TermSelector childTerm: allSelectors) {
            //only one parent
            ProofTermReferenceTarget childTarget = new ProofTermReferenceTarget(lastNode, childTerm);
            Set<ProofTermReferenceTarget> directParents = proofWithTwoSubstitutionsAndSkips.getReferenceGraph().findDirectParents(childTarget, proofWithTwoSubstitutionsAndSkips);
            Assert.assertTrue(directParents.size() == 1);
            Assert.assertTrue(HistoryProofUtils.compareTerms(childTarget, directParents.iterator().next(), proofWithTwoSubstitutionsAndSkips));
        }

    }

    /**
     * Test the specialities of let expansions and their influence on computing direct parents
     * TODO: not fully possible yet
     */
    @Test
    public void testLetParents() throws FormatException, RuleException{
        Proof letExpansionAntec = pm.getProofForPVC("max/else/Post");
        letExpansionAntec.setScriptTextAndInterpret("substitute on='... ((?m: let m := x :: !(m < y))) ... |-';\n");

        ReferenceGraph graph = letExpansionAntec.getReferenceGraph();

        ProofNodeSelector lastNode = ProofUtils.computeProofNodeSelector("0");
        ProofTermReferenceTarget notLtXY = new ProofTermReferenceTarget(lastNode, new TermSelector("A.0"));
        ProofTermReferenceTarget ltXY = new ProofTermReferenceTarget(lastNode, new TermSelector("A.0.0"));
        ProofTermReferenceTarget y = new ProofTermReferenceTarget(lastNode, new TermSelector("A.0.0.1"));
        ProofTermReferenceTarget x = new ProofTermReferenceTarget(lastNode, new TermSelector("A.0.0.0"));

        Set<ProofTermReferenceTarget> parentsnotltXY = graph.findDirectParents(notLtXY, letExpansionAntec);
        Set<ProofTermReferenceTarget> directParents = graph.findDirectParents(ltXY, letExpansionAntec);
        for (ProofTermReferenceTarget proofTermReferenceTarget: parentsnotltXY ) {
            System.out.println(HistoryProofUtils.getTerm(proofTermReferenceTarget, letExpansionAntec));

        }
        System.out.println(parentsnotltXY);
        System.out.println(directParents);

    }

    /**
     * This test test that an added Term via addHypothesis only has a scriptreference as parent and no direct parents
     * of type ProofReferenceTarget
     * @throws FormatException
     */
    @Test
    public void testAddedTermWithScriptReference() throws FormatException {
        Proof proofConj = pm.getProofForPVC("simpleConjunction/Post");
        proofConj.setScriptTextAndInterpret("addHypothesis  with='a == b';");
        TestUtil.assertNoException(proofConj.getFailures());
        ProofNodeSelector lastNode = ProofUtils.computeProofNodeSelector("0");
        ProofTermReferenceTarget b = new ProofTermReferenceTarget(lastNode, new TermSelector("A.1"));
        Set<ProofTermReferenceTarget> directParents = proofConj.getReferenceGraph().findDirectParents(b, proofConj);
        Assert.assertTrue(directParents.isEmpty());
        System.out.println(proofConj.getReferenceGraph());
        Set<ScriptReferenceTarget> scriptReferenceTargetSet = proofConj.getReferenceGraph().allSuccessorsWithType(b, ScriptReferenceTarget.class);
        Assert.assertFalse(scriptReferenceTargetSet.isEmpty());
        Assert.assertTrue(scriptReferenceTargetSet.size() == 1);
        ScriptReferenceTarget next = scriptReferenceTargetSet.iterator().next();
        Assert.assertEquals(1, next.getNode().getBeginToken().getLine());
    }

    @Test
    public void testReplacedTerm() throws Exception {
        Proof proofDisj = pm.getProofForPVC("simpleSplit/Post");
        proofDisj.setScriptTextAndInterpret("orRight on= '|- _ || _';");
        TestUtil.assertNoException(proofDisj.getFailures());
        ProofNodeSelector lastNode = ProofUtils.computeProofNodeSelector("0");
        ProofTermReferenceTarget right = new ProofTermReferenceTarget(lastNode, new TermSelector("S.0.1"));
        System.out.println(proofDisj.getReferenceGraph());
        Set<ProofTermReferenceTarget> directParents = proofDisj.getReferenceGraph().findDirectParents(right, proofDisj);
        Assert.assertEquals(1, directParents.size());
        ProofTermReferenceTarget directParentTarget = directParents.iterator().next();
        Assert.assertEquals(new TermSelector("S.0.0.1"), directParentTarget.getTermSelector());
        Assert.assertTrue(HistoryProofUtils.compareTerms(right, directParentTarget, proofDisj));

        //proofDisj.setScriptTextAndInterpret("orRight on= '|- _ || _';\n plus_0 on='|- ... ((?m: a + 0)) ...';");


        Proof proof = pm.getProofForPVC("simpleSplit/Post.1");
        proof.setScriptTextAndInterpret("andRight on= '|- _ && _';");
        ProofNodeSelector lastNodeP = ProofUtils.computeProofNodeSelector("0");
        ProofTermReferenceTarget select = new ProofTermReferenceTarget(lastNodeP, new TermSelector("S.0"));
        Set<ProofTermReferenceTarget> directParentsP = proof.getReferenceGraph().findDirectParents(select, proof);
        Assert.assertTrue(directParentsP.size() == 2);
        //TODO, here we want distinction between reoccurrence and context/explanation

    }

}
