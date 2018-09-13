/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
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
        return "[$eq<set<object>>($mod_1, m), $eq<int>($decr_1, $plus(p, 1)), " +
                "$eq<int>(local_1, p), $eq<int>(r_1, local_1), $gt(p, 0), $gt(local_1, 0)]";
    }

    @Override
    protected String expectedSuccedent(String pathIdentifier) {
        return "[$gt(r_1, 0)]";
    }

    private static String SSA_TEST =
            "method m(a: int, b: int) returns (r: int) " +
                    "requires a == 42 \n" +
                    "ensures r > 0 {\n" +
                    "  var local: int;\n" +
                    "  while a > 0 \n" +
                    "    invariant a+r==0 \n" +
                    "    decreases a\n" +
                    "  {\n" +
                    "    local := r;\n" +
                    "    r := r + 1;\n" +
                    "    a := a - 1;\n" +
                    "    b := local;\n" +
                    "  }}";

    private static String SSA_EXPECTED[] = {
            "$eq<set<object>>($mod_1, $empty), " +
                    "$eq<int>($decr_1, 0), $eq<int>(a, 42) " +
                    "|- $eq<int>($plus(a, r), 0)",
            "$eq<set<object>>($mod_1, $empty), " +
                    "$eq<int>($decr_1, 0), " +
                    "$eq<int>($decr_1_1, a_1), " +
                    "$eq<int>(local_2, r_1), " +
                    "$eq<int>(r_2, $plus(r_1, 1)), " +
                    "$eq<int>(a_2, $minus(a_1, 1)), " +
                    "$eq<int>(b_2, local_2), " +
                    "$eq<int>(a, 42), " +
                    "$eq<int>($plus(a_1, r_1), 0), " +
                    "$gt(a_1, 0) |- $eq<int>($plus(a_2, r_2), 0)",
            "$eq<set<object>>($mod_1, $empty), " +
                    "$eq<int>($decr_1, 0), " +
                    "$eq<int>(a, 42), " +
                    "$eq<int>($plus(a_1, r_1), 0), " +
                    "$not($gt(a_1, 0)) |- $gt(r_1, 0)"
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
            assertEquals(SSA_EXPECTED[i], sequent.toString());
        }
    }

    private static String SSA_LINEAR =
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


    private static String SSA_LINEAR_EXPECTED =
            "$eq<set<object>>($mod_1, $empty), $eq<int>($decr_1, 0), " +
                    "$eq<int>(local_1, 0), " +
                    "$eq<int>(r_1, $plus(local_1, 1)), " +
                    "$eq<int>(local_2, $plus(r_1, 1)), " +
                    "$eq<int>(r_2, $plus(local_2, 1)), " +
                    "$eq<int>(local_3, $plus(r_2, 1)), " +
                    "$eq<int>(r_3, $plus(local_3, 1))" +
                    " |- $gt(r_3, 0)";

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

}
