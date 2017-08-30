package edu.kit.iti.algover.rules.impl;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;

import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ImmutableList;

@RunWith(JUnitParamsRunner.class)
public class PropositionalExpanderTest {

    private MapSymbolTable symbTable;

    public Object[][] parametersForTestExpansion() {
        return new Object[][]{
                {"(a && b)", SequentPolarity.ANTECEDENT, false, "[[a, b] ==> []]"},
                {"(a && b)", SequentPolarity.ANTECEDENT, true, "[[a, b] ==> []]"},
                {"(a && b)", SequentPolarity.SUCCEDENT, false, "[[] ==> [$and(a, b)]]"},
                {"(a && b)", SequentPolarity.SUCCEDENT, true, "[[] ==> [a], [] ==> [b]]"},

                {"(a || b)", SequentPolarity.ANTECEDENT, false, "[[$or(a, b)] ==> []]"},
                {"(a || b)", SequentPolarity.ANTECEDENT, true, "[[a] ==> [], [b] ==> []]"},
                {"(a || b)", SequentPolarity.SUCCEDENT, false, "[[] ==> [a, b]]"},
                {"(a || b)", SequentPolarity.SUCCEDENT, true, "[[] ==> [a, b]]"},

                {"(a ==> b)", SequentPolarity.ANTECEDENT, false, "[[$imp(a, b)] ==> []]"},
                {"(a ==> b)", SequentPolarity.ANTECEDENT, true, "[[] ==> [a], [b] ==> []]"},
                {"(a ==> b)", SequentPolarity.SUCCEDENT, false, "[[a] ==> [b]]"},
                {"(a ==> b)", SequentPolarity.SUCCEDENT, true, "[[a] ==> [b]]"},

                {"(a ==> b) ==> (c ==> d)", SequentPolarity.SUCCEDENT, true,
                        "[[c] ==> [a, d], [b, c] ==> [d]]"},

                {"(a ==> b) ==> (c ==> d)", SequentPolarity.SUCCEDENT, false,
                        "[[$imp(a, b), c] ==> [d]]"},

                {"a && b && c && d", SequentPolarity.SUCCEDENT, true,
                        "[[] ==> [a], [] ==> [b], [] ==> [c], [] ==> [d]]"
                }
        };
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("a", Sort.BOOL));
        map.add(new FunctionSymbol("b", Sort.BOOL));
        map.add(new FunctionSymbol("c", Sort.BOOL));
        map.add(new FunctionSymbol("d", Sort.BOOL));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }


    @Test
    @Parameters
    public void testExpansion(String formulaString,
                              SequentPolarity polarity, Boolean allowSplit,
                              String expected) throws Exception {

        Term formula = TermParser.parse(symbTable, formulaString);
        PropositionalExpander pex = new PropositionalExpander();

        ImmutableList<?> result = pex.expand(formula, polarity, allowSplit);

        assertEquals(expected, result.toString());
    }
}
