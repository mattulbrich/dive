/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.KnownRegression;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.AlphaNormalisation;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.hamcrest.core.StringContains;
import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.rules.ExpectedException;

import static org.junit.Assert.*;

public class LetSubstitutionRuleTest {

    private final TermBuilder builder = new TermBuilder(new BuiltinSymbols());

    @Test
    public void testBasicSubstitution() throws Exception {
        testSubstitution(parse("let x := 5 :: x >= 5"), parse("5 >= 5"));
    }

    private void testSubstitution(Term letTerm, Term expected) throws Exception {
        PrettyPrint print = new PrettyPrint();
        print.setPrintingFix(true);

        System.out.println("input:    " + print.print(letTerm).toString());
        System.out.println("expected: " + print.print(expected).toString());
        Term result = applyLetSubstition(letTerm);
        System.out.println("result:   " + print.print(result).toString());
        assertEquals(expected, result);
        assertTrue(AlphaNormalisation.isNormalised(result));
    }

    private static Term parse(String str) throws Exception {
        BuiltinSymbols symbols = new BuiltinSymbols();
        symbols.addFunctionSymbol(new FunctionSymbol("i", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("a", Sort.get("array", Sort.INT)));

        return TermParser.parse(symbols, str);
    }

    private Term applyLetSubstition(Term letTerm) throws TermBuildException, RuleException {
        ProofNode proofNode = ProofMockUtil.mockProofNode(null, new Term[]{letTerm}, new Term[0]);

        LetSubstitutionRule letRule = new LetSubstitutionRule();

        ProofRuleApplication application = letRule.considerApplication(proofNode, proofNode.getSequent(), new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0));

        assertEquals(ProofRuleApplication.Applicability.APPLICABLE, application.getApplicability());
        assertFalse(application.isRefinable());
        assertEquals(1, application.getBranchCount());
        assertEquals(1, application.getBranchInfo().get(0).getReplacements().size());
        assertTrue(application.getBranchInfo().get(0).getAdditions().isEmpty());
        assertTrue(application.getBranchInfo().get(0).getDeletions().isEmpty());

        return application.getBranchInfo().get(0).getReplacements().get(0).getSnd();
    }

    @Test
    public void testLetShadowing() throws Exception {
        testSubstitution(
                parse("let x := 5 :: " +
                        " x == (let x := 6 :: x)"),
                parse("5 == (let x := 6 :: x)")
        );
    }

    @Test
    public void testOldState() throws Exception {
        testSubstitution(
                parse("let x := i :: let i := i + 1 :: i == (let i := x :: i)"),
                parse("let i_1 := i + 1 :: i_1 == (let i := i :: i)")
        );
    }


    @Test
    public void testLetQuantifier() throws Exception {
        testSubstitution(
                parse("let x := 5 :: " +
                          "(forall x :: x>0) == (x>0)"),
                parse("(forall x :: x>0) == (5>0)")
        );
    }

    @Test
    public void testLetShadowingParallel() throws Exception {
        testSubstitution(
                parse("let x := 5 :: " +
                        " x == (let x, y := 6, x :: x)"),
                parse("5 == (let x, y := 6, 5 :: x)")
        );
    }

    /**
     * Conflicting Names must be resoluted with {@link AlphaNormalisation} in newly created terms
     * @throws Exception
     */
    @Test
    public void testNameClash() throws Exception {
        testSubstitution(
                parse("let x := i :: forall i :: i == x"),
                parse("forall i_1 :: i_1 == i"));
    }

    /**
     * In Case of "$heap" and "$oldheap" substitution always the right heap must be chosen.
     * Name clashes will occur. So AlphaNormalisation in the LetSubstitutionRule application is needed.
     * AlphaNormalisation replaces inner let wrongfully.
     * See {@link edu.kit.iti.algover.term.builder.AlphaNormalisationTest#testNormalise(String, String)} last parameter
     * is necessary.
     * @throws Exception
     */
    @Test
    public void testAlteredHeap() throws Exception {
        testSubstitution(
                parse("let $oldheap := $heap :: " +
                        "let $heap := $heap[a[0] := a[0] + 1] :: " +
                        "$array2seq<int>($heap, a)" +
                        "  == (let $heap := $oldheap :: $array2seq<int>($heap, a))"),
                // expect something like
                parse("let $heap_1 := $heap[a[0] := a[0] + 1] ::" +
                        " $array2seq<int>($heap_1, a) ==" +
                        " (let $heap := $heap :: $array2seq<int>($heap, a))"));
        /* This fails. The last last statement of the result is $array2seq<int>($heap_1, a))
            So the sequences are creates with the array from the same heap.
         */

    }

    // Substitution must be conflict-free, otherwise the semantics
    // change illegally.
    @Test
    public void testConflictingSubstitution() throws Exception {
        Term t1 = parse("let y := 42 :: let x := y :: let y := 27 :: x>0");
        Term t2 = parse("let x := 42 :: let y := 27 :: x>0");
        testSubstitution(t1, t2);

        // applying the middle substitution in t2 must result in a conflict:
        //     let y := 42 :: let x := y :: let y := 27 :: x
        // ->  let y := 42 :: let y := 27 :: y
        // ->  27
        // whereas t1,t2 is equal to 42

        Term[] letTerm = { t1 };
        ProofNode proofNode = ProofMockUtil.mockProofNode(null, letTerm, new Term[0]);
        LetSubstitutionRule letRule = new LetSubstitutionRule();
        ProofRuleApplication application = letRule.considerApplication(proofNode,
                proofNode.getSequent(),
                new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0, 1));

        assertEquals(application.getApplicability(), Applicability.NOT_APPLICABLE);
    }

    @Test
    public void testApplicationExceptionLet() throws Exception {
        Term t1 = parse("let y := 42 :: let x := y :: let y := 27 :: x");
        Term t2 = t1.getTerm(0);

        try {
            TestUtil.callStatic(LetSubstitutionRule.class, "applyLetSubstitution", t2);
            fail("Should throw exception!");
        } catch(RuntimeException ex) {
            Throwable cause = ex.getCause().getCause();
            Assert.assertSame(RuleException.class, cause.getClass());
            Assert.assertEquals("Substitution induces a conflict: x",  cause.getMessage());
        }
//        Object result = TestUtil.callStatic(LetSubstitutionRule.class, "applyLetSubstitution", t2);
//        Term expected = parse("let y := 42 :: let y_1 := 27 :: y").getTerm(0);
//        assertEquals(expected, result);
    }

    @Test
    public void testApplicationExceptionQuant() throws Exception {
        Term t1 = parse("let y := 42 :: let x := y :: forall y :: x>0");
        Term t2 = t1.getTerm(0);

        try {
            TestUtil.callStatic(LetSubstitutionRule.class, "applyLetSubstitution", t2);
            fail("Should throw exception!");
        } catch(RuntimeException ex) {
            Throwable cause = ex.getCause().getCause();
            Assert.assertSame(RuleException.class, cause.getClass());
            Assert.assertEquals("Substitution induces a conflict: x",  cause.getMessage());
        }
//        Object result = TestUtil.callStatic(LetSubstitutionRule.class, "applyLetSubstitution", t2);
//        Term expected = parse("let y := 42 :: forall y_1 :: y>0").getTerm(0);
//        assertEquals(expected, result);
    }

}
