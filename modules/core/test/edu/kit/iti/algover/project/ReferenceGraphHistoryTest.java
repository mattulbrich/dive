package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import junitparams.JUnitParamsRunner;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Set;

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphHistoryTest {

    public Proof proofBranched;

    public Proof proofWithRemoval;

    @Before
    public void testProjectLoad(){

        XMLProjectManager pm = null;
        try {
            URL resource = getClass().getResource("./referenceGraphTest");

            pm = new XMLProjectManager(new File(resource.getFile()), "config.xml");
            pm.reload();

            proofBranched = pm.getProofForPVC("max/else/Post.1");
            String script2 = "substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n"+
                    "skip;\n"+
                    "substitute on='|- ... ((?match: let m := x :: m >= x && m >= y)) ...'; \n"+
                    "skip;\n"+
                    "andRight on='|- ... ((?match: x >= x && x >= y)) ...';\n"+
                    "cases {\n"+
                    "    case match \"case 1\": {\n"+
                    "        skip;\n"+
                    "    }\n"+
                    "    case match \"case 2\": {\n"+
                    "        skip;\n"+
                    "    }\n"+
                    "}\n";
            proofBranched.setScriptTextAndInterpret(script2);

            //has addlist+delList
            proofWithRemoval = pm.getProofForPVC("ff/Post");
            proofWithRemoval.setScriptTextAndInterpret("andLeft on='... ((?match: a >= 0 && a < 100)) ... |-';\n"+
                    "removeAssumption on='... ((?match: a + 1 == a + 1 && a > 0 ==> b >= 0)) ... |-';\nskip;\n");



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

    @Test
    public void testHistory(){

    }

    private void testHistory(ProofNodeSelector pns, TermSelector childTerm, Proof proof){
        try {
            Term term1 = childTerm.selectSubterm(pns.get(proof).getSequent());
            Set<ProofTermReferenceTarget> directParents = proof.getGraph().computeHistory(new ProofTermReferenceTarget(pns, childTerm), proof);
            System.out.println("pns = " + pns);
            System.out.println("term1 = " + term1);
            //System.out.println("proofFormula = " + proofFormula);
            for (ProofTermReferenceTarget directParent : directParents) {
                Term term2 = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(proof).getSequent());
                System.out.println("Node = " + directParent.getProofNodeSelector());
                System.out.println("term2 = " + term2);
                //Assert.assertFalse(term == proofFormula);
            }
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }
}
