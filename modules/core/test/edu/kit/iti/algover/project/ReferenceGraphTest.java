package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import javafx.beans.property.IntegerProperty;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphTest {

    public Proof proof;

    public Proof proof2;

 //   public String termSelector;
 //   public String path;
    @Test
    @Parameters(method="parametersTotestProof")
    public void whenWithAnnotationProvidedParams_thentestForProof(String a, String b, boolean bo){
       Assert.assertEquals(testForProof(a,b), bo);
    }

    private Object[][] parametersTotestProof() {
        return new Object[][]
                {
                        new Object[]{"0,0", "A.0", true},
                        new Object[]{"0,0", "A.0.0", true},
                        new Object[]{"0,0", "A.0.0.0", true},
                        new Object[]{"0,0", "A.0.0.1", true},
                        new Object[]{"0", "A.0", false},
                        new Object[]{"0", "A.0.0", false},
                        new Object[]{"0", "A.0.0.0", true},
                        new Object[]{"0", "A.0.0.1", true},

                };
    }


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
    public boolean testForProof(String path, String termSelector){
         return testDirectlyChangedTerm(path, termSelector, proof);
    }


    public boolean testDirectlyChangedTerm(String pathChild, String termSelectorString, Proof currentProof){
        boolean ret = false;
        String[] pathStringArray = pathChild.split(",");
        int[] path = Arrays.stream(pathStringArray).mapToInt(value -> Integer.parseInt(value)).toArray();
        ProofNodeSelector pns = new ProofNodeSelector(path);
        try {
            TermSelector termSelector = new TermSelector(termSelectorString);
            Set<ProofTermReferenceTarget> directParents = currentProof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), currentProof);
            Term proofFormula = termSelector.selectSubterm(pns.get(currentProof).getSequent());
            System.out.println("Test for proof node "+pns+" term "+ proofFormula);

            for (ProofTermReferenceTarget directParent : directParents) {
                Term term = directParent.getTermSelector().selectSubterm(directParent.getProofNodeSelector().get(currentProof).getSequent());
                ret = term == proofFormula;
                if(!ret){
                    System.out.println("term = " + term+ " and "+proofFormula+ " are not equal");
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
