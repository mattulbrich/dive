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
import junitparams.Parameters;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Arrays;
import java.util.Set;

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphTest {

    public Proof proof;

    public Proof proof2;

 //   public String termSelector;
 //   public String path;
    @Test
    @Parameters(method="unchangedFormulas")
    public void testUnchanged(String a, String b){
       Assert.assertEquals(testMethodForProof(a,b), true);
    }

    @Test
    @Parameters(method="changedFormulas")
    public void testChanged(String a, String b){
        Assert.assertEquals(testMethodForProof(a,b), false);
    }


    private Object[][] unchangedFormulas() {
        return new Object[][]
                {
                       new Object[]{"0,0", "A.0"},
                        new Object[]{"0,0", "A.0.0"},
                        new Object[]{"0,0", "A.0.0.0"},
                        new Object[]{"0,0", "A.0.0.1"},
                        new Object[]{"0", "S.0"},


                };
    }

    private Object[][] changedFormulas(){
        return new Object[][]
                {
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
    public void testProjectLoad(){

        XMLProjectManager pm = null;
        try {
            URL resource = getClass().getResource("./referenceGraphTest");

            pm = new XMLProjectManager(new File(resource.getFile()), "config.xml");
            pm.reload();
            proof = pm.getProofForPVC("max/else/Post");
            proof.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                    "substitute on='|- ... ((?match: let m := x :: m > 1)) ...';\n");

            proof2 = pm.getProofForPVC("max/else/Post.1");
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
            proof2.setScriptTextAndInterpret(script2);



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
    public boolean testMethodForProof(String path, String termSelector){
         return testDirectParent(path, termSelector, proof);
    }

    private ProofNodeSelector computeProofNodeSelector(String pathChild){
        String[] pathStringArray = pathChild.split(",");
        int[] path = Arrays.stream(pathStringArray).mapToInt(value -> Integer.parseInt(value)).toArray();
        ProofNodeSelector pns = new ProofNodeSelector(path);
        return pns;
    }

    /**
     * False iff term or formula changed from pathChild to direct parent, true iff term or formula unchanged
     * @param pathChild
     * @param termSelectorString
     * @param currentProof
     * @return
     */
    public boolean testDirectParent(String pathChild, String termSelectorString, Proof currentProof){
        boolean ret = false;
        ProofNodeSelector pns = computeProofNodeSelector(pathChild);

        try {
            TermSelector termSelector = new TermSelector(termSelectorString);
            Set<ProofTermReferenceTarget> directParents = currentProof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), currentProof);
            Term proofFormula = termSelector.selectSubterm(pns.get(currentProof).getSequent());
            System.out.println("Test for proof node "+ pns +" term "+ proofFormula);

            for (ProofTermReferenceTarget directParent : directParents) {
                Term term = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(currentProof).getSequent());
                if(ret = term == proofFormula){
                    System.out.println("Term value " + term + " has not changed from node "+pns.getParentSelector()+" to "+pns);
                    if(directParent.getTermSelector() != termSelector){
                        System.out.println("But position has changed");
                        ret = false;
                    } else {
                        System.out.println("and position has not changed");
                    }

                } else {

                    System.out.println("term = " + term+ " and "+proofFormula+ " are not identical");
                }
            }
        } catch (FormatException e) {
            e.printStackTrace();
        } catch (RuleException e) {
            e.printStackTrace();
        }
        return ret;

    }


    public void testNotDirectlyChangedTerm(){
        int[] path = {0,0};
        ProofNodeSelector pns = new ProofNodeSelector(path);
        try {
            TermSelector termSelector = new TermSelector("A.0");
            Set<ProofTermReferenceTarget> directParents = proof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), proof);
            Term proofFormula = termSelector.selectSubterm(pns.get(proof).getSequent());
            for (ProofTermReferenceTarget directParent : directParents) {
                Term term = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(proof).getSequent());
                Assert.assertTrue(term == proofFormula);
            }
        } catch (FormatException e) {
            e.printStackTrace();
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }


    public void testDirectlyChangedTermUnBranched(){
        int[] path = {0,0};
        ProofNodeSelector pns = new ProofNodeSelector(path);
        try {
            TermSelector termSelector = new TermSelector("S.0");
            Set<ProofTermReferenceTarget> directParents = proof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), proof);
            Term proofFormula = termSelector.selectSubterm(pns.get(proof).getSequent());
            for (ProofTermReferenceTarget directParent : directParents) {
                Term term = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(proof).getSequent());
                Assert.assertFalse(term == proofFormula);
            }
        } catch (FormatException e) {
            e.printStackTrace();
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }

    public void testDirectlyChangedTermBranched(){
        int[] path = {0,0,0,0,1,0};
        ProofNodeSelector pns = new ProofNodeSelector(path);
        try {
            TermSelector termSelector = new TermSelector("S.0.1");
            Set<ProofTermReferenceTarget> directParents = proof2.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), proof2);
            Term proofFormula = termSelector.selectSubterm(pns.get(proof2).getSequent());
            for (ProofTermReferenceTarget directParent : directParents) {
                Term term = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(proof2).getSequent());
                System.out.println("term = " + term);
                System.out.println("proofFormula = " + proofFormula);
                Assert.assertTrue(term == proofFormula);

            }

        } catch (FormatException e) {
            e.printStackTrace();
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }



    public void testHistory(){
        int[] path = {0,0};
        ProofNodeSelector pns = new ProofNodeSelector(path);
        try {
            TermSelector termSelector = new TermSelector("A.0.0");
            Term term1 = termSelector.selectSubterm(pns.get(proof).getSequent());
            Set<ProofTermReferenceTarget> directParents = proof.getGraph().computeHistory(new ProofTermReferenceTarget(pns, termSelector), proof);
            System.out.println("pns = " + pns);
            System.out.println("term1 = " + term1);
            //System.out.println("proofFormula = " + proofFormula);
            for (ProofTermReferenceTarget directParent : directParents) {
                Term term2 = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(proof).getSequent());
                System.out.println("Node = " + directParent.getProofNodeSelector());
                System.out.println("term2 = " + term2);
                //Assert.assertFalse(term == proofFormula);
            }
        } catch (FormatException e) {
            e.printStackTrace();
        } catch (RuleException e) {
            e.printStackTrace();
        }
    }



}
