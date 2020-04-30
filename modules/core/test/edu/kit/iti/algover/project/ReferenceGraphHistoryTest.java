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
import edu.kit.iti.algover.util.ProofUtils;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.Set;

//TODO check
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

   private Object[][] testCasesProofWithRemoval(){
        return new Object[][]
                {
                        new Object[]{"0,0,0", "A.0", 4, "[ProofTermReferenceTarget{proofNodeSelector=0.0, termSelector=A.0}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0}, ProofTermReferenceTarget{proofNodeSelector=0, termSelector=A.0}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0.0}]"},
                        new Object[]{"0,0,0", "A.1", 3, "[ProofTermReferenceTarget{proofNodeSelector=0, termSelector=A.2}, ProofTermReferenceTarget{proofNodeSelector=0.0, termSelector=A.1}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0.1}]"},
                        new Object[]{"0,0,0", "S.0", 3, "[ProofTermReferenceTarget{proofNodeSelector=0.0, termSelector=S.0}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=S.0}, ProofTermReferenceTarget{proofNodeSelector=0, termSelector=S.0}]"},
                        new Object[]{"0,0,0", "A.0.1", 3, "[ProofTermReferenceTarget{proofNodeSelector=0, termSelector=A.0.1}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0.0.1}, ProofTermReferenceTarget{proofNodeSelector=0.0, termSelector=A.0.1}]"},
                        new Object[]{"0,0", "A.0", 3, "[ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0}, ProofTermReferenceTarget{proofNodeSelector=0, termSelector=A.0}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0.0}]"},
                        new Object[]{"0,0,0", "A.1.0", 3, "[ProofTermReferenceTarget{proofNodeSelector=0, termSelector=A.2.0}, ProofTermReferenceTarget{proofNodeSelector=0.0, termSelector=A.1.0}, ProofTermReferenceTarget{proofNodeSelector=<root>, termSelector=A.0.1.0}]"},


                };

    }
    @Test
    @Parameters(method="testCasesProofWithRemoval")
    public void testHistoryInProofWithRemoval(String path, String selector, int size, String exp) throws FormatException {
        ProofNodeSelector pns = ProofUtils.computeProofNodeSelector(path);
        TermSelector childTerm =  new TermSelector(selector);
        Set<ProofTermReferenceTarget> actual = computeHistoryVerbose(pns, childTerm, proofWithRemoval);
        Assert.assertTrue(actual.size() == size);
        Assert.assertEquals(exp, actual.toString());
    }



    @Test
    public void testHistory() throws FormatException {
        ProofNodeSelector pns = ProofUtils.computeProofNodeSelector("0,0,0");
        TermSelector childTerm =  new TermSelector("A.0");
        Set<ProofTermReferenceTarget> directParents = proofWithRemoval.getGraph().computeHistory(new ProofTermReferenceTarget(pns, childTerm), proofWithRemoval);
        System.out.println("directParents = " + directParents);
    }

    private Set<ProofTermReferenceTarget> computeHistoryVerbose(ProofNodeSelector pns, TermSelector childTerm, Proof proof){
        Set<ProofTermReferenceTarget> directParents = Collections.emptySet();
        try {
            Term term1 = childTerm.selectSubterm(pns.get(proof).getSequent());
            directParents = proof.getGraph().computeHistory(new ProofTermReferenceTarget(pns, childTerm), proof);
            System.out.println("\nHistory for term '"+term1+"' in Proof Node = " + pns);

            //System.out.println("proofFormula = " + proofFormula);
            for (ProofTermReferenceTarget directParent : directParents) {
                Term term2 = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(proof).getSequent());
                System.out.println("Parent in Node = " + directParent.getProofNodeSelector()+" term2 = " + term2);
            }
        } catch (RuleException e) {
            e.printStackTrace();
        }
        return directParents;
    }
}
