/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import static org.junit.Assert.assertNotNull;

import java.util.ArrayList;
import java.util.Collection;

import edu.kit.iti.algover.util.ImmutableList;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

import static org.junit.Assert.*;

@RunWith(JUnitParamsRunner.class)
public class TermMatcherTest {

    private MapSymbolTable symbTable;

    public String[][] parametersForTestMatching() {
        return new String[][] {
            { "?x + ?y", "2 + 3", "[[?x => 2 / 0, ?y => 3 / 1]]" },
            { "_ + _", "2 + 3", "[[_0 => 2 / 0, _1 => 3 / 1]]" },
            { "?x + ?x", "2 + 2", "[[?x => 2 / 0]]" },
            { "f(f(_))", "f(f(f(5)))", "[[_0 => f(5) / 0.0]]" },
            { "h(__)", "h(1,2)", "[[_0 => 1 / 0, _1 => 2 / 1]]" },
            { "exists i:int :: ?phi", "exists i:int :: i*i == 4",
              "[[?phi => $eq<int>($times(i, i), 4) / 0]]" },
            { "...1...", "2+1", "[[...0 => 1 / 1]]" },
            { "... ?x+_ ...", "(2+3)+(4+5)",
               "[[?x => $plus(2, 3) / 0, _0 => $plus(4, 5) / 1, ...0 => $plus($plus(2, 3), $plus(4, 5)) / ], "
              + "[?x => 2 / 0.0, _0 => 3 / 0.1, ...0 => $plus(2, 3) / 0], "
              + "[?x => 4 / 1.0, _0 => 5 / 1.1, ...0 => $plus(4, 5) / 1]]" },
        };
    }

    public String[][] parametersForNoMatch() {
        return new String[][] {
            { "?x + ?x", "2 + 3" },
            { "?x + ?x", "2 * 2" },
            { "f(0)", "g(0)" },
            { "forall i:int :: ?phi", "forall j:int :: true" },
        };
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("f", Sort.INT, Sort.INT));
        map.add(new FunctionSymbol("g", Sort.INT, Sort.INT));
        map.add(new FunctionSymbol("h", Sort.INT, Sort.INT, Sort.INT));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test @Parameters
    public void testMatching(String schem, String conc, String expMatch) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = TreeTermTranslatorTest.parse(schem, true);
        Term schemTerm = ttt.build(t);

        t = TreeTermTranslatorTest.parse(conc, true);
        Term concTerm = ttt.build(t);

        TermMatcher m = new TermMatcher();
        Iterable<Matching> result = m.match(schemTerm, concTerm);

        assertEquals(expMatch, result.toString());
    }

    @Test @Parameters
    public void noMatch(String schem, String conc) throws Exception {
        assertNotNull(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t = TreeTermTranslatorTest.parse(schem, true);
        Term schemTerm = ttt.build(t);

        t = TreeTermTranslatorTest.parse(conc, true);
        Term concTerm = ttt.build(t);

        TermMatcher m = new TermMatcher();
        Iterable<Matching> result = m.match(schemTerm, concTerm);

        assertEquals(ImmutableList.nil(), result);
    }
}