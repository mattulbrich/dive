package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.ProofMockUtil;
import org.junit.Test;

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
    }

    private static Term parse(String str) throws Exception {
        return TermParser.parse(new BuiltinSymbols(), str);
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
    public void testLetShadowingParallel() throws Exception {
        testSubstitution(
                parse("let x := 5 :: " +
                        " x == (let x, y := 6, x :: x)"),
                parse("5 == (let x, y := 6, 5 :: x)")
        );
    }


    // Substitution must be conflict-free, otherwise the semantics
    // change illegally.
    @Test
    public void testConflictingSubstitution() throws Exception {
        Term t1 = parse("let y := 42 :: let x := y :: let y := 27 :: x");
        Term t2 = parse("let x := 42 :: let y := 27 :: x");
        Term t3 = parse("let y := 42 :: let y_1 := 27 :: y");
        // t3 must NOT be (let y := 27 :: y) which is equivalent to 27
        // whereas t1,t2 is equal to 42
        // substitution may fail with exception if need be.
        testSubstitution(t1, t2);
        testSubstitution(t1.getTerm(0), t3.getTerm(0));
    }
}
