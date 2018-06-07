/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.InterpreterUtils;
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
                {"let x := true :: _", "let x := 5 :: 2*x == 10", "[]"},
                {"let x := ?y :: _", "let x := 5 :: x+5 == 10", "[[_0 => $eq<int>($plus(x, 5), 10) / 0, ?y => 5 / 0]]"},
                {"let x := ?y :: ?x+?y == _", "let x := 15 :: x+15 == 15", "[[?x => x / 0.0.0, ?y => 15 / 0.0.1, _0 => 15 / 0.1]]"},
                {"let x := 5 :: x+5 == 10", "let x := 5 :: x+5 == 10", "[[]]"},
                {"let x := ?y :: ?x+?y == 10", "let x := 5 :: x+5 == 10", "[[?x => x / 0.0.0, ?y => 5 / 0.0.1]]"},
                {"?x + ?y", "2 + 3", "[[?x => 2 / 0, ?y => 3 / 1]]"},
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
                {"2+3", "2+3", "[[]]"},
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

    public String[][][] parametersForSequentMatch() {
        return new String[][][]{
                //SchemAntec, SchemSucc, ConcAntec, ConcSucc, Exp
                {{"?x", "g(?x)"}, {}, {"f(0)", "g(4)", "g(1)"}, {}, {"[]"}},
                {{"f(1)"}, {"g(f(1))"}, {"f(1)"}, {"g(f(1))", "f(4)"}, {"[[]]"}},
                {{"(... ?x ...) + (... ?y ...) == ?z"}, {}, {"2 + 3 == 5"}, {}, {"[[?x => 2 / A.0.0.0, ...0 => 2 / A.0.0.0, ?y => 3 / A.0.0.1, ...1 => 3 / A.0.0.1, ?z => 5 / A.0.1]]"}},
                {{"f(?x)"}, {"g(f(?x))"}, {"f(1)"}, {"g(f(1))", "f(4)"}, {"[[?x => 1 / A.0.0]]"}},
                {{"_"}, {"_"}, {"f(1)"}, {"g(1)", "f(1)"}, {"[[_0 => f(1) / A.0, _1 => g(1) / S.0], [_0 => f(1) / A.0, _1 => f(1) / S.1]]"}},
                {{"... ?x+_ ..."}, {"f(?x)"}, {"(2+3)+(4+5) == 1"}, {"f(2)", "f(4)"}, {"[[?x => 2 / A.0.0.0.0, _0 => 3 / A.0.0.0.1, ...0 => $plus(2, 3) / A.0.0.0], [?x => 4 / A.0.0.1.0, _0 => 5 / A.0.0.1.1, ...0 => $plus(4, 5) / A.0.0.1]]"}},
                {{"... ?x + 5 ..."}, {"... 4 + ?x ..."}, {"2 + 5 > 1"}, {"4 + 2 > 3 && true"}, {"[[?x => 2 / A.0.0.0, ...0 => $plus(2, 5) / A.0.0, ...1 => $plus(4, 2) / S.0.0.0]]"}},
                {{"?X+?Y"}, {"f(?Y)"}, {"1+2", "2+1", "1+1"}, {"f(2)", "f(1)"}, {"[[?X => 1 / A.0.0, ?Y => 2 / A.0.1], [?X => 2 / A.1.0, ?Y => 1 / A.1.1], [?X => 1 / A.2.0, ?Y => 1 / A.2.1]]"}},
                {{"2+1"}, {}, {"f(1)==f(1)", "2+1", "2+1"}, {}, {"[[], []]"}},
                {{"...let x := 5 :: x+5 == 10..."}, {}, {"let x := 5 :: x+5 == 10"}, {}, {"[[...0 => (let x := 5 :: $eq<int>($plus(x, 5), 10)) / A.0]]"}},

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

    @Test
    @Parameters
    public void SequentMatch(String[] schemSeqAntec, String[] schemSeqSucc, String[] concrSeqAntec, String[] concrSeqSucc, String[] exp) throws Exception {
        ImmutableList<Matching> matchings = matchSeqHelper(schemSeqAntec, schemSeqSucc, concrSeqAntec, concrSeqSucc);
        assertEquals(exp[0], matchings.toString());
    }


    private ImmutableList<Matching> matchSeqHelper(String[] schemSeqAntec, String[] schemSeqSucc, String[] concrSeqAntec, String[] concrSeqSucc) throws Exception {
        assertNotNull(symbTable);


        Sequent schemSeq = InterpreterUtils.createTestSequentHelper(schemSeqAntec, schemSeqSucc, symbTable, true);
        Sequent concSeq = InterpreterUtils.createTestSequentHelper(concrSeqAntec, concrSeqSucc, symbTable, true);

        //    OldSequentMatcher sm = new OldSequentMatcher();
        SequentMatcher sm = new SequentMatcher();
        ImmutableList<Matching> match = sm.match(schemSeq, concSeq);

/*        if (match.isEmpty()) {
            System.out.format("SchemaSequent: %s does not match concrete sequent: %s",
                    schemSeq,
                    concSeq);
        } else {
            System.out.format("SchemaSequent: %s  matches concrete sequent: %s",
                    schemSeq,
                    concSeq);
            System.out.println(" with matching = " + match);
            for (Matching m : match) {
                System.out.println("m = " + m);
            }
        }*/
        return match;
    }


}
