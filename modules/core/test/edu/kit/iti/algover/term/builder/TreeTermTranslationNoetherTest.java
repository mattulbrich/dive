/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.assertEquals;

public class TreeTermTranslationNoetherTest {

    private MapSymbolTable symbTable;

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("$decr_1", Sort.INT));
        map.add(new FunctionSymbol("$decr_2", Sort.INT));
        map.add(new FunctionSymbol("$decr_3", Sort.INT));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test
    public void testNoetherSmall() throws Exception {
        DafnyTree less = new DafnyTree(DafnyParser.NOETHER_LESS);
        {
            DafnyTree vars = new DafnyTree(DafnyParser.LISTEX);
            vars.addChild(new DafnyTree(DafnyParser.ID, "$decr_1"));
            less.addChild(vars);
        }
        {
            DafnyTree listex = new DafnyTree(DafnyParser.LISTEX);
            listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "1"));
            less.addChild(listex);
        }
        assertEquals("(NOETHER_LESS (LISTEX $decr_1) (LISTEX 1))", less.toStringTree());

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        Term result = ttt.build(less);

        TermBuilder tb = new TermBuilder(symbTable);
        {
            Term leq = tb.lessEqual(tb.zero, tb.id("$decr_1"));
            Term l = tb.less(tb.id("$decr_1"), tb.intLiteral(1));
            Term and = tb.and(leq, l);
            assertEquals(and, result);
        }
    }

    @Test
    public void testNoether() throws Exception {

        DafnyTree less = new DafnyTree(DafnyParser.NOETHER_LESS);
        {
            {
                DafnyTree vars = new DafnyTree(DafnyParser.LISTEX);
                vars.addChild(new DafnyTree(DafnyParser.ID, "$decr_1"));
                vars.addChild(new DafnyTree(DafnyParser.ID, "$decr_2"));
                vars.addChild(new DafnyTree(DafnyParser.ID, "$decr_3"));
                less.addChild(vars);
            }
            {
                DafnyTree listex = new DafnyTree(DafnyParser.LISTEX);
                listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "1"));
                listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "2"));
                listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "3"));
                less.addChild(listex);
            }
        }
        assertEquals("(NOETHER_LESS (LISTEX $decr_1 $decr_2 $decr_3) (LISTEX 1 2 3))", less.toStringTree());

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        Term result = ttt.build(less);

        TermBuilder tb = new TermBuilder(symbTable);
        Term expected;
        expected = TermParser.parse(symbTable,
                "0 <= $decr_1 && $decr_1 < 1 ||" +
                        "$decr_1 == 1 && 0 <= $decr_2 && $decr_2 < 2 ||" +
                        "$decr_1 == 1 && $decr_2 == 2 && 0 <= $decr_3 && $decr_3 < 3");

        /*{ // This code produced the comparison in wrong order!
            Term rng1, rng2, rng3;
            Term eq1, eq2;
            {

                Term leq = tb.lessEqual(tb.zero, tb.intLiteral(1));
                Term l = tb.less(tb.intLiteral(1), tb.id("$decr_1"));
                eq1 = tb.eq(tb.intLiteral(1), tb.id("$decr_1"));
                rng1 = tb.and(leq, l);
            }
            {
                Term leq = tb.lessEqual(tb.zero, tb.intLiteral(2));
                Term l = tb.less(tb.intLiteral(2), tb.id("$decr_2"));
                eq2 = tb.eq(tb.intLiteral(2), tb.id("$decr_2"));
                rng2 = tb.and(tb.and(eq1, leq), l);
            }
            {
                Term leq = tb.lessEqual(tb.zero, tb.intLiteral(3));
                Term l = tb.less(tb.intLiteral(3), tb.id("$decr_3"));
                rng3 = tb.and(tb.and(tb.and(eq1, eq2), leq), l);
            }
            expected = tb.or(tb.or(rng1, rng2), rng3);
        }*/

        assertEquals(expected.toString(), result.toString());
        assertEquals(expected, result);
    }


}
