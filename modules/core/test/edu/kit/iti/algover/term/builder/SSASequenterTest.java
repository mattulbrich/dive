/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.antlr.runtime.RecognitionException;
import org.junit.Test;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class SSASequenterTest extends SequenterTest {

    @Override
    protected PVCSequenter makeSequenter() {
        return new SSASequenter();
    }

    @Override
    protected String expectedAntecedent(String pathIdentifier) {
        return "[$eq<set<object>>($mod_1, $union<object>(m, $freshObjects($heap))), $eq<int>($decr_1, $plus(p, 1)), " +
                "$eq<heap>($oldheap_1, $heap), $eq<int>(local_1, p), " +
                "$eq<int>(r_1, local_1), $gt(p, 0), $gt(local_1, 0)]";
    }

    @Override
    protected String expectedSuccedent(String pathIdentifier) {
        return "[(let $heap := $oldheap_1 :: $gt(r_1, 0))]";
    }

    private static String SSA_TEST =
            "method m(a: int, b: int) returns (r: int) " +
                    "requires a == 42 \n" +
                    "ensures r > 0 {\n" +
                    "  var la := a;\n" +
                    "  var lb := b;\n" +
                    "  r := 0;\n" +
                    "  while la > 0 \n" +
                    "    invariant la+r==0 \n" +
                    "    decreases la\n" +
                    "  {\n" +
                    "    var local := r;\n" +
                    "    r := r + 1;\n" +
                    "    la := la - 1;\n" +
                    "    lb := local;\n" +
                    "  }}";

    private static String SSA_EXPECTED[] = {
            "[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                    "[Path]: $eq<int>($decr_1, 0), " +
                    "[Path]: $eq<heap>($oldheap_1, $heap), " +
                    "[Path]: $eq<int>(la_1, a), " +
                    "[Path]: $eq<int>(lb_1, b), " +
                    "[Path]: $eq<int>(r_1, 0), " +
                    "[PreCond]: $eq<int>(a, 42) " +
                    "|- [Assertion]: $eq<int>($plus(la_1, r_1), 0)",
            "[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                    "[Path]: $eq<int>($decr_2, 0), " +
                    "[Path]: $eq<heap>($oldheap_1, $heap), " +
                    "[Path]: $eq<int>(la_1, a), " +
                    "[Path]: $eq<int>(lb_1, b), " +
                    "[Path]: $eq<int>(r_1, 0), " +
                    "[Path]: $eq<int>($decr_1_1, la_2), " +
                    "[Path]: $eq<int>(local_1, r_2), " +
                    "[Path]: $eq<int>(r_3, $plus(r_2, 1)), " +
                    "[Path]: $eq<int>(la_3, $minus(la_2, 1)), " +
                    "[Path]: $eq<int>(lb_3, local_1), " +
                    "[PreCond]: $eq<int>(a, 42), " +
                    "[Assumption]: $eq<int>($plus(la_2, r_2), 0), " +
                    "[PathCond]: $gt(la_2, 0) " +
                    "|- [Assertion]: $eq<int>($plus(la_3, r_3), 0)",
            "[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                    "[Path]: $eq<int>($decr_1, 0), " +
                    "[Path]: $eq<heap>($oldheap_1, $heap), " +
                    "[Path]: $eq<int>(la_1, a), " +
                    "[Path]: $eq<int>(lb_1, b), " +
                    "[Path]: $eq<int>(r_1, 0), " +
                    "[PreCond]: $eq<int>(a, 42), " +
                    "[Assumption]: $eq<int>($plus(la_2, r_2), 0), " +
                    "[PathCond]: $not($gt(la_2, 0)) |- [Assertion]: $gt(r_2, 0)"
    };

    @Test
    public void testSSAWithLoop() throws Exception {
        InputStream is = new ByteArrayInputStream(SSA_TEST.getBytes());
        DafnyTree top = ParserTest.parseFile(is, null);

        Project p = TestUtil.mockProject(top);

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(SSA_EXPECTED.length, results.size());

        for (int i = 0; i < SSA_EXPECTED.length; i++) {
            SymbexPath path = results.get(i).split().get(0);
            PVCSequenter sequenter = makeSequenter();
            Sequent sequent = sequenter.translate(path, makeTable(method), null);
            assertEquals("case " + i, SSA_EXPECTED[i], sequent.toString());
        }
    }

    private static final String SSA_LINEAR =
            "method m() returns (r: int) ensures r>0" +
                    "{\n" +
                    "  var local: int;\n" +
                    "  local := 0;\n" +
                    "  r := local + 1;\n" +
                    "  local := r + 1;\n" +
                    "  r := local + 1;\n" +
                    "  local := r + 1;\n" +
                    "  r := local + 1;\n" +
                    "}";


    private static final String SSA_LINEAR_EXPECTED =
            "[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                    "[Path]: $eq<int>($decr_1, 0), " +
                    "[Path]: $eq<heap>($oldheap_1, $heap), " +
                    "[Path]: $eq<int>(local_1, 0), " +
                    "[Path]: $eq<int>(r_1, $plus(local_1, 1)), " +
                    "[Path]: $eq<int>(local_2, $plus(r_1, 1)), " +
                    "[Path]: $eq<int>(r_2, $plus(local_2, 1)), " +
                    "[Path]: $eq<int>(local_3, $plus(r_2, 1)), " +
                    "[Path]: $eq<int>(r_3, $plus(local_3, 1))" +
                    " |- [Assertion]: $gt(r_3, 0)";

    private static final String HEAP_EXPECTED =
            "[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                    "[Path]: $eq<int>($decr_1, 0), " +
                    "[Path]: $eq<heap>($oldheap_1, $heap), " +
                    "[Path]: $eq<heap>($heap_1, $array_store<int>($heap, a, 0, 1)), " +
                    "[Path]: $eq<heap>($heap_2, $store<C,int>($heap_1, c, C$$f, 2)) " +
                    "|- [Assertion]: (let $heap := $oldheap_1 :: " +
                    "$eq<int>($select<C,int>($heap, c, C$$f), $array_select<int>($heap, a, 0)))";


    // revealed a bug in numbering
    @Test
    public void testSSALinear() throws Exception {
        InputStream is = new ByteArrayInputStream(SSA_LINEAR.getBytes());
        DafnyTree top = ParserTest.parseFile(is, null);

        Project p = TestUtil.mockProject(top);

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(1, results.size());

        SymbexPath path = results.get(0).split().get(0);
        PVCSequenter sequenter = makeSequenter();
        Sequent sequent = sequenter.translate(path, makeTable(method), null);
        assertEquals(SSA_LINEAR_EXPECTED, sequent.toString());
    }

    @Test
    public void testDoubleAssume() throws Exception {
        ByteArrayInputStream is = new ByteArrayInputStream(
                "method m() requires 1==1 ensures true { assume 1==1; }".getBytes());
        DafnyTree top = ParserTest.parseFile(is, null);

        Project p = TestUtil.mockProject(top);

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(1, results.size());

        SymbexPath path = results.get(0).split().get(0);
        PVCSequenter sequenter = makeSequenter();
        Sequent sequent = sequenter.translate(path, makeTable(method), null);
        assertEquals("[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                "[Path]: $eq<int>($decr_1, 0), " +
                "[Path]: $eq<heap>($oldheap_1, $heap), " +
                "[PreCond, Assumption]: $eq<int>(1, 1) " +
                "|- [Assertion]: true", sequent.toString());
    }

    // Heaps have not been implemented at one point.
    @Test
    public void testHeapAssignments() throws Exception {
        Project p = TestUtil.mockProject("class C { var f: int; }" +
                "method m(a:array<int>, c:C) ensures old(c.f == a[0]) { a[0] := 1; c.f := 2; }");

        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());

        SymbexPath path = results.get(0).split().get(0);
        assertEquals("Post", path.getPathIdentifier());
        PVCSequenter sequenter = makeSequenter();
        Sequent sequent = sequenter.translate(path, makeTable(method, p), null);
        assertEquals(HEAP_EXPECTED, sequent.toString());
    }

    protected void checkSequentWithOld(SymbolTable table, Sequent sequent) throws Exception {
        assertEquals("[Path]: $eq<set<object>>($mod_1, $freshObjects($heap)), " +
                "[Path]: $eq<int>($decr_1, 0), " +
                "[Path]: $eq<heap>($oldheap_1, $heap), " +
                "[Path]: $eq<heap>($heap_1, $store<C,int>($heap, c, C$$i, 0)), " +
                "[Path]: $eq<heap>($heap_2, $store<C,int>($heap_1, c, C$$i, " +
                   "$plus((let $heap := $oldheap_1 :: $select<C,int>($heap, c, C$$i)), 1)))" +
                " |- [Assertion]: $eq<int>($select<C,int>($heap_2, c, C$$i), " +
                "$plus((let $heap := $oldheap_1 :: $select<C,int>($heap, c, C$$i)), 1))", sequent.toString());
    }

}
