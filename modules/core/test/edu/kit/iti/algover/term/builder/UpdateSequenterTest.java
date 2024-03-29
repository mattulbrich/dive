/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.*;

import java.io.InputStream;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.parser.TermParser;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class UpdateSequenterTest extends SequenterTest {

    protected String expectedSuccedent(String string) {
        return "[(let $mod := $union<object>(m, $freshObjects($heap)) :: (let $decr := $plus(p, 1) :: " +
                "(let $oldheap := $heap :: (let local := p :: (let r := local :: " +
                "(let $heap := $oldheap :: $gt(r, 0)))))))]";
    }

    protected String expectedAntecedent(String string) {
        return "[$gt(p, 0), (let $mod := $union<object>(m, $freshObjects($heap)) :: (let $decr := $plus(p, 1) :: " +
                "(let $oldheap := $heap :: (let local := p :: $gt(local, 0)))))]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new UpdateSequenter();
    }

    // used to debug a problem.
    @Test
    public void testLetProblem1() throws Exception {
        InputStream is = getClass().getResourceAsStream("gcd.dfy");
        DafnyTree top = ParserTest.parseFile(is, null);
        // SyntacticSugarVistor.visit(top);
        Project p = TestUtil.mockProject(top);

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("gcd");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());

        PVCSequenter sequenter = makeSequenter();
        for (SymbexPath paths : results) {
            for (SymbexPath path : paths.split()) {
                Sequent sequent = sequenter.translate(path, makeTable(method), null);
            }
        }
    }

    /* That's the code:
     * i := x + 3;
     * assume i > 0;
     * i := i + 2;
     * i := a[i];
     * r := i;
     */

    public String[][] parametersForTestReferenceMap() {
        return new String[][] {
            { "A.0", null, null },
            { "A.0.0", null, null },
            { "A.0.0.0", null, null },
            { "A.0.0.0.0", null, null },
            { "A.0.0.0.0.0", "$gt(i, 0)", "(> i 0)" },
            { "A.0.0.0.0.0.0", "i", "i" },
            { "A.0.0.0.0.0.1", "0", "0" },
            { "A.0.0.0.0.1.0", "x", "x" },
            { "A.0.0.0.0.1.1", "3", "3" },
            { "A.0.0.0.0.1", "$plus(x, 3)", "(+ x 3)" },
            { "A.0.0.0.1", "$heap", "$heap" }, // artificial
            { "A.0.0.1", "0", "0" }, // artificial
            { "A.0.1", "$freshObjects($heap)", "(CALL $freshObjects (ARGS $heap))" }, // artificial
            { "A.0.1.0", "$heap", "$heap" }, // artificial

            { "S.0", null, null },
            { "S.0.0", null, null },
            { "S.0.0.0", null, null },
            { "S.0.0.0.0", null, null },
            { "S.0.0.0.0.0", null, null },
            { "S.0.0.0.0.0.0", null, null },
            { "S.0.0.0.0.0.0.0", null, null },
            { "S.0.0.0.0.0.0.0.0", "$gt(r, 0)", "(> r 0)" },
            { "S.0.0.0.0.0.0.0.0.0", "r", "r" },
            { "S.0.0.0.0.0.0.0.0.1", "0", "0" },
            { "S.0.0.0.0.0.0.0.1", "i", "i" },
            { "S.0.0.0.0.0.0.1", "$array_select<int>($heap, a, i)", "(ARRAY_ACCESS a i)" },
            { "S.0.0.0.0.0.0.1.0", null, null},
            { "S.0.0.0.0.0.0.1.1", "a", "a" },
            { "S.0.0.0.0.0.0.1.2", "i", "i" },
            { "S.0.0.0.0.0.1", "$plus(i, 2)", "(+ i 2)" },
            { "S.0.0.0.0.0.1.0", "i", "i" },
            { "S.0.0.0.0.0.1.1", "2", "2" },
            { "S.0.0.0.0.1", "$plus(x, 3)", "(+ x 3)" },
            { "S.0.0.0.0.1.0", "x", "x" },
            { "S.0.0.0.0.1.1", "3", "3" },
            { "S.0.0.0.1", "$heap", "$heap" },
            { "S.0.0.1", "0", "0" },
            { "S.0.1", "$freshObjects($heap)", "(CALL $freshObjects (ARGS $heap))" }, // artificial
            { "S.0.1.0", "$heap", "$heap" }, // artificial
        };
    }

    @Test @Parameters
    public void testReferenceMap(String sel, String term, String expected) throws Exception {
        InputStream is = getClass().getResourceAsStream("referencesTest.dfy");
        DafnyTree top = ParserTest.parseFile(is, null);
        Project p = TestUtil.mockProject(top);
        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(3, results.size());

        PVCSequenter sequenter = makeSequenter();
        SymbexPath path = results.get(0);
        Map<TermSelector, DafnyTree> map = new HashMap<>();
        Sequent sequent = sequenter.translate(path, makeTable(method), map);

        if (TestUtil.VERBOSE) {
            System.out.println(sequent);
            System.out.println(map);
            map.forEach((ts, tree) -> System.out.printf("%20s %s%n", ts, tree.toStringTree()));
        }

        TermSelector selector = new TermSelector(sel);
        Term actual = selector.selectSubterm(sequent);

        DafnyTree fromMap = map.get(selector);
        if(term == null) {
            assertNull(fromMap);
        } else {
            assertEquals(term, actual.toString());
            assertNotNull(fromMap);
            assertEquals(expected, fromMap.toStringTree());
        }

//        for (Map.Entry<TermSelector, DafnyTree> en : map.entrySet()) {
//            Term x = en.getKey().selectSubterm(sequent);
//            System.out.println(en.getKey() + " / " + x + " : " + en.getValue().toStringTree());
//        }

    }

    // revealed a bug
    @Test
    public void testFieldAssignments() throws Exception {
        Project p = TestUtil.mockProject("class C { var fld:C; method m() ensures true { fld := this; this.fld := this; } }");
        Symbex symbex = new Symbex();
        DafnyMethod method = p.getClass("C").getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(1, results.size());
        SymbexPath path = results.get(0);

        PVCSequenter sequenter = makeSequenter();
        SymbolTable table = makeTable(method, p);
        Sequent sequent = sequenter.translate(path, table, null);

        assertEquals("|- [Assertion]: (let $mod := $freshObjects($heap) :: " +
                "(let $decr := 0 :: " +
                "(let $oldheap := $heap :: " +
                "(let $heap := $store<C,C>($heap, this, C$$fld, this) :: " +
                "(let $heap := $store<C,C>($heap, this, C$$fld, this) :: true)))))", sequent.toString());
    }

    protected void checkSequentWithOld(SymbolTable table, Sequent sequent) throws Exception {

        assertEquals("|- [Assertion]: (let $mod := $freshObjects($heap) :: " +
                "(let $decr := 0 :: (let $oldheap := $heap :: " +
                "(let $heap := $store<C,int>($heap, c, C$$i, 0) :: " +
                "(let $heap := $store<C,int>($heap, c, C$$i, $plus((let $heap := $oldheap :: " +
                "$select<C,int>($heap, c, C$$i)), 1)) :: $eq<int>($select<C,int>($heap, c, C$$i), $plus((let $heap := $oldheap :: " +
                "$select<C,int>($heap, c, C$$i)), 1)))))))", sequent.toString());

        Term inlined = LetInlineVisitor.inline(sequent.getSuccedent().get(0).getTerm());
        assertEquals(TermParser.parse(table, "c.i@$heap[c.i := 0][c.i:=c.i@$heap+1] == c.i + 1"), inlined);
    }
}
