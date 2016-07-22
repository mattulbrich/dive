/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;

import org.antlr.runtime.CommonToken;
import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

public class TreeTermTranslationNoetherTest {

    private MapSymbolTable symbTable;

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("#d_0", Sort.INT));
        map.add(new FunctionSymbol("#d_1", Sort.INT));
        map.add(new FunctionSymbol("#d_2", Sort.INT));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test
    public void testNoetherSmall() throws Exception {
        DafnyTree less = new DafnyTree(DafnyParser.NOETHER_LESS);
        {
            DafnyTree listex = new DafnyTree(DafnyParser.LISTEX);
            less.addChild(new DafnyTree(DafnyParser.ID, "#d"));
            listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "1"));
            less.addChild(listex);
        }
        assertEquals("(NOETHER_LESS #d (LISTEX 1))", less.toStringTree());

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        Term result = ttt.build(less);

        TermBuilder tb = new TermBuilder(symbTable);
        {
            Term leq = tb.lessEqual(tb.zero, tb.intLiteral(1));
            Term l = tb.less(tb.intLiteral(1), tb.id("#d_0"));
            Term and = tb.and(leq, l);
            assertEquals(and, result);
        }
    }

   @Test
    public void testNoether() throws Exception {

        DafnyTree less = new DafnyTree(DafnyParser.NOETHER_LESS);
        {
            DafnyTree listex = new DafnyTree(DafnyParser.LISTEX);
            less.addChild(new DafnyTree(DafnyParser.ID, "#d"));
            less.addChild(listex);
            {
                listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "1"));
                listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "2"));
                listex.addChild(new DafnyTree(DafnyParser.INT_LIT, "3"));
            }
        }
        assertEquals("(NOETHER_LESS #d (LISTEX 1 2 3))", less.toStringTree());

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);
        Term result = ttt.build(less);

        TermBuilder tb = new TermBuilder(symbTable);
        Term expected;
        {
            Term rng1, rng2, rng3;
            Term eq1, eq2;
            {
                Term leq = tb.lessEqual(tb.zero, tb.intLiteral(1));
                Term l = tb.less(tb.intLiteral(1), tb.id("#d_0"));
                eq1 = tb.eq(tb.intLiteral(1), tb.id("#d_0"));
                rng1 = tb.and(leq, l);
            }
            {
                Term leq = tb.lessEqual(tb.zero, tb.intLiteral(2));
                Term l = tb.less(tb.intLiteral(2), tb.id("#d_1"));
                eq2 = tb.eq(tb.intLiteral(2), tb.id("#d_1"));
                rng2 = tb.and(tb.and(eq1, leq), l);
            }
            {
                Term leq = tb.lessEqual(tb.zero, tb.intLiteral(3));
                Term l = tb.less(tb.intLiteral(3), tb.id("#d_2"));
                rng3 = tb.and(tb.and(tb.and(eq1, eq2), leq), l);
            }
            expected = tb.or(tb.or(rng1, rng2), rng3);
        }

        assertEquals(expected.toString(), result.toString());
        assertEquals(expected, result);

    }


}
