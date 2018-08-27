package edu.kit.iti.algover.util;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.term.parser.TermParser;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import static edu.kit.iti.algover.rules.TermSelector.SequentPolarity.ANTECEDENT;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

@RunWith(JUnitParamsRunner.class)
public class RuleUtilTest {

    private static BuiltinSymbols symbols;

    static {
        symbols = new BuiltinSymbols();
        symbols.addFunctionSymbol(new FunctionSymbol("x", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("y", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("f", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("b1", Sort.BOOL));
        symbols.addFunctionSymbol(new FunctionSymbol("b2", Sort.BOOL));
        symbols.addFunctionSymbol(new FunctionSymbol("b3", Sort.BOOL));
        symbols.addFunctionSymbol(new FunctionSymbol("b4", Sort.BOOL));
        symbols.addFunctionSymbol(new FunctionSymbol("i1", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("i2", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("i3", Sort.INT));
        symbols.addFunctionSymbol(new FunctionSymbol("i4", Sort.INT));
    }

    private final Sequent exampleSequent =
            new Sequent(
                    Arrays.asList(
                            parse(0, "x > (let f := 3 :: y + (f + 3))"),
                            parse(1, "x > (y - 5)"),
                            parse(2, "y - 5 == x")
                    ),
                    Arrays.asList(
                            parse(0, "x > (y - 5)"),
                            parse(1, "let m := 0 :: x + m == x")
                    ));

    private static ProofFormula parse(int index, String term) {
        return new ProofFormula(parseTerm(term));
    }

    private static Term parseTerm(String term) {
        try {
            return TermParser.parse(symbols, term);
        } catch (DafnyException|DafnyParserException e) {
            throw new RuntimeException(e);
        }
    }

    public Object[][] parametersSubtermInSequent() throws FormatException {
        return new Object[][]{
                {new TermSelector("A.1.1"), parseTerm("y - 5")},
                // The f in (f + 3)
                {new TermSelector("A.0.1.0.1.0"), new VariableTerm("f", Sort.INT)},
                {null, parseTerm("x + y")}
        };
    }

    @Test
    @Parameters(method = "parametersSubtermInSequent")
    public void testSubtermInSequent(TermSelector selector, Term term) {
        assertEquals(
                Optional.ofNullable(selector),
                RuleUtil.matchSubtermInSequent(term::equals, exampleSequent));
    }

    public Object[][] parametersTopLevelAntecedent() {
        return new Object[][]{
                {2, parseTerm("y - 5 == x")},
                {1, parseTerm("x > (y - 5)")},
                {null, parseTerm("y - 5")}
        };
    }

    @Test
    @Parameters(method = "parametersTopLevelAntecedent")
    public void testTopLevelAntecedent(Integer expectedIndex, Term toLookFor) {
        assertEquals(
                Optional.ofNullable(expectedIndex),
                RuleUtil.matchTopLevelInAntedecent(toLookFor::equals, exampleSequent));
    }

    @Test
    public void testOther() throws FormatException {
        assertEquals("Should find right match for any subtraction",
                Optional.of(new TermSelector("A.1.1")),
                RuleUtil.matchSubtermInSequent(this::isSubtractionTerm, exampleSequent));

        assertEquals("Always denying a match should return no match",
                Optional.empty(),
                RuleUtil.matchSubtermInSequent(term -> false, exampleSequent));

        assertEquals("Accepting any term should return the first term",
                Optional.of(new TermSelector("A.0")),
                RuleUtil.matchSubtermInSequent(term -> true, exampleSequent));
    }

    private boolean isSubtractionTerm(Term term) {
        if (!(term instanceof ApplTerm)) {
            return false;
        }
        ApplTerm applTerm = (ApplTerm) term;
        if (!applTerm.getFunctionSymbol().equals(BuiltinSymbols.MINUS)) {
            return false;
        }
        return true;
    }

    public Object[][] parametersGetNumNegations() throws DafnyException, DafnyParserException {
        Sequent s = TermParser.parseSequent(symbols, "!b1, !!b1, !(!b1 && b2) |- b3");
        return new Object[][]{
                {1, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0)},
                {2, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 1, 0)},
                {1, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 1)},
                {2, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 2, 0, 0)},
                {1, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 2, 0, 1)},
                {0, s, new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0)}
        };
    }

    @Test
    @Parameters(method = "parametersGetNumNegations")
    public void testGetNumNegations(int expectedNum, Sequent s, TermSelector ts) throws RuleException {
        assertEquals(expectedNum, RuleUtil.getNumNegations(ts, s, 0));
    }

    public Object[][] parametersGetTruePolarity() throws DafnyException, DafnyParserException {
        Sequent s = TermParser.parseSequent(symbols, "!b1, !!b1, !(!b1 && b2) |- b3");
        return new Object[][]{
                {TermSelector.SequentPolarity.SUCCEDENT, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0)},
                {TermSelector.SequentPolarity.ANTECEDENT, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 1, 0)},
                {TermSelector.SequentPolarity.SUCCEDENT, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 1)},
                {TermSelector.SequentPolarity.ANTECEDENT, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 2, 0, 0)},
                {TermSelector.SequentPolarity.SUCCEDENT, s, new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 2, 0, 1)},
                {TermSelector.SequentPolarity.SUCCEDENT, s, new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0)}
        };
    }

    @Test
    @Parameters(method = "parametersGetTruePolarity")
    public void testGetTruePolarity(TermSelector.SequentPolarity expectedPol, Sequent s, TermSelector ts) throws RuleException {
        assertEquals(expectedPol, RuleUtil.getTruePolarity(ts, s));
    }
}
