package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.TestInfrastructure;
import edu.kit.iti.algover.util.TestUtil;
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

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphTest {

    public Proof proof;

    public Proof proof2;

    public Proof proof3;

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
    public void testProjectLoad(){

        XMLProjectManager pm = null;
        try {
            URL resource = getClass().getResource("./referenceGraphTest");

            pm = new XMLProjectManager(new File(resource.getFile()), "config.xml");
            pm.reload();
            proof = pm.getProofForPVC("max/else/Post");
            proof.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                    "substitute on='|- ... ((?match: let m := x :: m > 1)) ...';\n"+"skip;\n"+"skip;\n");

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

            //has addlist
            proof3 = pm.getProofForPVC("ff/Post");
            proof3.setScriptTextAndInterpret("andLeft on='... ((?match: a >= 0 && a < 100)) ... |-';\n"+
                  //  "removeAssumption on='... ((?match: a + 1 == a + 1)) ... |-';\n"
                    "removeAssumption on='... ((?match: a + 1 == a + 1 && a > 0 ==> b >= 0)) ... |-';\n");



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
    public void testSkipRule() throws RuleException, FormatException {

        ProofNodeSelector lastNode = computeProofNodeSelector("0,0,0,0");
        Sequent lastSeq = lastNode.get(proof).getSequent();
        List<TermSelector> allSelectors = computeAllSelectors(lastSeq);
        allSelectors.forEach(termSelector -> {
            Assert.assertTrue(isFormulaUnchangedInDirectParent("0,0,0,0", termSelector.toString(), proof));
        });
        ProofNodeSelector lastNodeBefore = computeProofNodeSelector("0,0,0");
        Sequent lastSeqBefore = lastNodeBefore.get(proof).getSequent();
        List<TermSelector> allSelectorsBefore = computeAllSelectors(lastSeqBefore);
        allSelectorsBefore.forEach(termSelector -> {
            Assert.assertTrue(isFormulaUnchangedInDirectParent("0,0,0", termSelector.toString(), proof));
        });


    }



    /**
     * Test parents of formulas that have been part of a replacement
     */
    @Test
    public void testReplacements(){

    }

    /**
     * Test the specialities of let expansions and their influence on computing direct parents
     */
    @Test
    public void testLetParents() {

    }



    /**
     * Test formulas that have been affected by additions or deletions
     * @throws FormatException
     * @throws RuleException
     */
    @Test
    public void testAddDelList() throws FormatException, RuleException {
//TODO
        Set<ProofTermReferenceTarget> proofTermReferenceTargets = computeDirectParents("0,0", "A.1", proof3);
        ProofNodeSelector pns = computeProofNodeSelector("0,0");
        TermSelector termSelector = new TermSelector("A.1");
        Term proofFormula = termSelector.selectSubterm(pns.get(proof3).getSequent());

        proofTermReferenceTargets.forEach(proofTermReferenceTarget -> {
            try {
                boolean comp = compareTerms(proofFormula, proofTermReferenceTarget, proof3);
                System.out.println("comp = " + comp);
            } catch (RuleException e) {
                e.printStackTrace();
            }
        });
    }

    public boolean testMethodForProof(String path, String termSelector){
         return isFormulaUnchangedInDirectParent(path, termSelector, proof);
    }

    public boolean testMethodForProof2(String path, String termSelector){
        return isFormulaUnchangedInDirectParent(path, termSelector, proof2);
    }


    @Test
    @Parameters(method="unchangedFormulas")
    public void testIfFormulaUnchangedInDirectParent(String a, String b){
        Assert.assertEquals(testMethodForProof(a,b), true);
    }

    @Test
    @Parameters(method="changedFormulas")
    public void testIfFormulaChangedInDirectParent(String a, String b){
        Assert.assertEquals(testMethodForProof(a,b), false);
    }


    private Set<ProofTermReferenceTarget> computeDirectParents(String pathChild, String termSelectorString, Proof currentProof) throws FormatException {
        ProofNodeSelector pns = computeProofNodeSelector(pathChild);
        TermSelector termSelector = new TermSelector(termSelectorString);
        Set<ProofTermReferenceTarget> directParents = currentProof.getGraph().findDirectParents(new ProofTermReferenceTarget(pns, termSelector), currentProof);
        return directParents;
    }

    private boolean compareTerms(Term termChild, ProofTermReferenceTarget target, Proof currentProof) throws RuleException {
        Term term = target.getTermSelector().selectSubterm(target.getProofNodeSelector().get(currentProof).getSequent());
        return termChild == term;

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




    private void testHistory(){
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

    @TestInfrastructure
    private ProofNodeSelector computeProofNodeSelector(String pathChild){
        String[] pathStringArray = pathChild.split(",");
        int[] path = Arrays.stream(pathStringArray).mapToInt(value -> Integer.parseInt(value)).toArray();
        ProofNodeSelector pns = new ProofNodeSelector(path);
        return pns;
    }


    @TestInfrastructure
    private static List<TermSelector> computeAllSelectors(Sequent lastSeq) throws FormatException {
        Set<TermSelector> selectors = new HashSet<>();
        List<ProofFormula> antecedent = lastSeq.getAntecedent();
        List<ProofFormula> succedent = lastSeq.getSuccedent();
        for (int i = 0; i < antecedent.size(); i++){
            ProofFormula form = antecedent.get(i);
            selectors.add(new TermSelector("A."+i));
            selectors.addAll(computeSelectorsWithCommonPrefix("A."+i, form.getTerm()));
        }
        for (int j = 0; j < succedent.size(); j++){
            ProofFormula form1 = succedent.get(j);
            selectors.add(new TermSelector("S."+j));
            selectors.addAll(computeSelectorsWithCommonPrefix("S."+j, form1.getTerm()));
        }
        return new ArrayList<>(selectors);
    }

    @TestInfrastructure
    private static Set<TermSelector> computeSelectorsWithCommonPrefix(String prefix, Term t) throws FormatException {
        Set<TermSelector> selectors = new HashSet<>();
        for(int i = 0; i<t.getSubterms().size(); i++) {
            selectors.add(new TermSelector(prefix+"."+i));
            selectors.addAll(computeSelectorsWithCommonPrefix(prefix+"."+i, t.getTerm(i)));
        }
        return selectors;
    }



}
