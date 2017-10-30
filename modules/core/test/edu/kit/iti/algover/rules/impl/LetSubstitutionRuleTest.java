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

    private Term applyLetSubstition(Term letTerm) throws TermBuildException, RuleException {
        ProofNode proofNode = ProofMockUtil.mockProofNode(null, new Term[] { letTerm }, new Term[0]);

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

    private void testSubstitution(Term letTerm, Term expected) throws Exception {
        PrettyPrint print = new PrettyPrint();
        print.setPrintingFix(true);

        System.out.println("input:    " + print.print(letTerm).toString());
        System.out.println("expected: " + print.print(expected).toString());
        Term result = applyLetSubstition(letTerm);
        System.out.println("result:   " + print.print(result).toString());
        assertEquals(expected, result);
    }

    private static Term parse(String str) throws DafnyParserException {
        return TermParser.parse(new BuiltinSymbols(), str);
    }

    @Test
    public void testBasicSubstitution() throws Exception {
        testSubstitution(parse("let x := 5 :: x >= 5"), parse("5 >= 5"));
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
}
