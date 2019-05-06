package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
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

@RunWith(JUnitParamsRunner.class)
public class ReferenceGraphDirectParentsTest {

    public Proof proofWithTwoSubstitutionsAndSkips;

    public Proof proofBranched;

    public Proof proofWithRemoval;

    public Proof proofWithReplacement;

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
            proofWithTwoSubstitutionsAndSkips = pm.getProofForPVC("max/else/Post");
            proofWithTwoSubstitutionsAndSkips.setScriptTextAndInterpret("substitute on='... ((?match: let m := x :: !(m < y))) ... |-';\n" +
                    "substitute on='|- ... ((?match: let m := x :: m > 1)) ...';\n"+"skip;\n"+"skip;\n");

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
    public void init(){
        System.out.println("Iniitialized");
    }

    @Test
    public void testSkipRule() throws RuleException, FormatException {

        ProofNodeSelector lastNode = computeProofNodeSelector("0,0,0,0");
        ProofNode proofNode = lastNode.get(proofWithTwoSubstitutionsAndSkips);
        Sequent lastSeq = proofNode.getSequent();
        List<TermSelector> allSelectors = computeAllSelectors(lastSeq);
        allSelectors.forEach(termSelector -> {
            Assert.assertTrue(isFormulaUnchangedInDirectParent("0,0,0,0", termSelector.toString(), proofWithTwoSubstitutionsAndSkips));
        });
        ProofNodeSelector lastNodeBefore = computeProofNodeSelector("0,0,0");
        Sequent lastSeqBefore = lastNodeBefore.get(proofWithTwoSubstitutionsAndSkips).getSequent();
        List<TermSelector> allSelectorsBefore = computeAllSelectors(lastSeqBefore);
        allSelectorsBefore.forEach(termSelector -> {
            Assert.assertTrue(isFormulaUnchangedInDirectParent("0,0,0", termSelector.toString(), proofWithTwoSubstitutionsAndSkips));
        });


    }



    /**
     * Test parents of formulas that have been part of a replacement
     */
    @Test
    public void testReplacements() throws RuleException, FormatException {
        //proofWithReplacement;
        Assert.assertFalse(isFormulaUnchangedInDirectParent("0,0", "A.0", proofWithReplacement));
        //SaG: atm the parent whole replaced formula is returned, therefore although term value is still part of whole formula it is consiedered as changed
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
     * Test the specialities of let expansions and their influence on computing direct parents
     */
    @Test
    public void testLetParents() {
//TODO
    }



    /**
     * Test formulas that have been affected by additions or deletions
     * @throws FormatException
     * @throws RuleException
     */
    @Test
    public void testDelList() throws FormatException, RuleException {
        ProofNodeSelector pns = computeProofNodeSelector("0,0");
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
                boolean comp = compareTerms(proofFormula, parent, proofWithRemoval);
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



    @TestInfrastructure
    public static ProofNodeSelector computeProofNodeSelector(String pathChild){
        String[] pathStringArray = pathChild.split(",");
        int[] path = Arrays.stream(pathStringArray).mapToInt(value -> Integer.parseInt(value)).toArray();
        ProofNodeSelector pns = new ProofNodeSelector(path);
        return pns;
    }


    @TestInfrastructure
    public static List<TermSelector> computeAllSelectors(Sequent lastSeq) throws FormatException {
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
