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
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Set;

public class ReferenceGraphTest {

    public Proof proof;

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

    @Test
    public void testDirectlyChangedTerm(){
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

    @Test
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
