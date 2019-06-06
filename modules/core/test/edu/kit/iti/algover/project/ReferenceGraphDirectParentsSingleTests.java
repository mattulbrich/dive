package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.HistoryProofUtils;
import edu.kit.iti.algover.util.ProofUtils;
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
import java.util.logging.Logger;

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
            proofWithTwoSubstitutionsAndSkips.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                    "substitute on='|- ... ((?match: let m := x :: m > 1)) ...';\n"+"skip;\n"+"skip;\n");

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
        proofWithTwoSubstitutionsAndSkips.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                "substitute on='|- ... ((?match: let m := x :: m > 1)) ...';\n"+"skip;");

        ProofNodeSelector lastNode = ProofUtils.computeProofNodeSelector("0,0,0");
        Sequent lastSeq = lastNode.get(proofWithTwoSubstitutionsAndSkips).getSequent();
        List<TermSelector> allSelectors = ProofUtils.computeAllSelectors(lastSeq);
        for (TermSelector childTerm: allSelectors) {
            //only one parent
            ProofTermReferenceTarget childTarget = new ProofTermReferenceTarget(lastNode, childTerm);
            Set<ProofTermReferenceTarget> directParents = proofWithTwoSubstitutionsAndSkips.getGraph().findDirectParents(childTarget, proofWithTwoSubstitutionsAndSkips);
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
        letExpansionAntec.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n");

        ReferenceGraph graph = letExpansionAntec.getGraph();

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


}
