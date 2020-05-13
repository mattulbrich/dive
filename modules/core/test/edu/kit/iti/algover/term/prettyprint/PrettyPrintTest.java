/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;

@RunWith(JUnitParamsRunner.class)
public class PrettyPrintTest {

    private static final Sort C = Sort.get("C");

    private SymbolTable st;

    public String[][] parametersForTestArithmetic() {
        return new String[][] {
            { "1 + 2" },
            { "1 + i1" },
            { "1 + (2 + 3)" },
            { "1 + 2 + 3" },
                {"1 + 2 - 3"},
            { "1 + 2 * 3" },
            { "1 * 2 + 3" },
            { "(1 + 2) * 3" },
            { "1 * (2 + 3)" },
            { "100 / (2 + 3)" },
            { "100 / 2 + 3" },
            { "100 / 2 * 3" },
            { "100 * 2 / 3" },
            { "1 < 2" },
            { "1 <= 2" },
            { "1 > 0" },
            { "1 >= 0" },
            { "1 + 2 >= 1 * 1" },
            { "1 + 1 == 2" },
            { "1 == i1" }, // revealed a bug
            { "-1" },
            { "- -1" },
        };
    }

    public String[][] parametersForTestLogic() {
        return new String[][] {
            { "true && false" },
            { "b1 ==> b1 && b1" },
            { "b1 && b1 ==> b1" },
            { "b1 ==> b1 ==> b1" },
            { "(b1 ==> b1) && b1" },
            { "b1 && (b1 || b1)" },
            { "! !b1" },
            { "!(b1 && b1)" },
            { "1 != 2" },
            { "b1 && (b1 && b1)" },
            { "b1 && b1 && b1" },
        };
    }

    public Object[][] parametersForTestWithLinebreak() {
        return new Object[][] {
            { "b1 && b1", "   b1\n&& b1", 5 },
            { "(b1 && b1) && b1", "   b1\n&& b1\n&& b1", 5 },
            { "(b1 || b1) || b1", "   b1\n|| b1\n|| b1", 5 },
            { "b1 && (b1 && b1)", "   b1\n&& (   b1\n    && b1)", 7 },
            { "b1 || b1 && b1",   "   b1\n||    b1\n   && b1", 7 }
        };
    }

    public String[][] parametersForTestSpecialFunctions() {
        return new String[][] {
            { "if i1 == 0 then i1 else 0" },
            { "i1 + (if i1 == 0 then i1 else 0)" },
            { "if b1 then let x := 0 :: x + 1 else if b1 then 0 else 1" }, // revealed a bug
            { "a.Length" }, { "a2.Length0" }, { "a2.Length1" },
        };
    }

    public String[][] parametersForTestHeap() {
        return new String[][]{
            { "o.f" },
            { "a[0]" },
            { "o.f@h2" },
            { "a[i1]@h2" },
            { "o.f@$heap[o.f := 3]" },
            { "a[i1]@$heap[a[0] := 42]" },
            { "$heap[o.f := 42]" },
            { "$heap[o.f := 4][o.f := 5][$anon($mod, h2)]" },
         //   { "let o.f := 4 :: o.f + 2" },  // well, some time in the future perhaps :)

            // Precedences
            { "o.f + 1"}, { "1 + o.f"},
            { "a[0] + 1" }, { "1 + a[0]" },
            { "1 + o.f@h2"}, { "o.f@h2 + 1"},
            { "1 + a[0]@h2"}, { "a[0]@h2 + 1"},
        };
    }

    public String[][] parametersForTestLetExpressions() {
        return new String[][] {
            { "let x := 0 :: x * 2" },
            { "1 + (let x := 0 :: x * 2)" },
                {"(let x := 0 :: x * 2) + 1"},
                {"let x := 0 :: let y := 0 :: x * y"},
                {"let x := 0 :: (let y := 0 :: x * y) * x"},
                {"let x, y := 1, 2 :: x + y"},  // revealed a bug
                {"let x := 0 :: if b1 then x else 0"},
                {"1 + (let x := 0 :: if b1 then x else 0)"}, // revealed a bug
        };
    }

    public String[][] parametersForTestADTExpressions() {
        return new String[][] {
            { "|sq|" }, { "|st|" }, { "st + st" }, { "sq + sq" },
            { "{1, 2, 3}" }, { "[1, 2, 3]"},
            { "sq[0]" },
        };
    }

    public String[][] parametersForTestSchemaExpressions() {
        return new String[][] {
            { "... (1 + 2) ..." },
            { "?on" },
            { "(?on: 1 + 2)" },
            { "_ ==> ?something" },
        };
    }

    public String[][] parametersForTestDafnyFunctions() {
        return new String[][] {
            { "o.cfct(0, o) == 0" },
            { "fct(0, o) && true" },
            { "o.cfct(0, o)@h2" },
            { "fct(0, o)@h2" },
            { "o.cfct(0, o)@$heap[o.f := 42]" },
        };
    }

    @Before
    public void setupTable() {
        st = new BuiltinSymbols();
        st.addFunctionSymbol(new FunctionSymbol("i1", Sort.INT));
        st.addFunctionSymbol(new FunctionSymbol("b1", Sort.BOOL));
        st.addFunctionSymbol(new FunctionSymbol("b2", Sort.BOOL));
        st.addFunctionSymbol(new FunctionSymbol("h2", Sort.HEAP));
        st.addFunctionSymbol(new FunctionSymbol("anything", Sort.INT, Sort.INT));
        st.addFunctionSymbol(new FunctionSymbol("a", Sort.get("array", Sort.INT)));
        st.addFunctionSymbol(new FunctionSymbol("a2", Sort.get("array2", Sort.INT)));

        st.addFunctionSymbol(new FunctionSymbol("sq", Sort.get("seq", Sort.INT)));
        st.addFunctionSymbol(new FunctionSymbol("st", Sort.get("set", Sort.INT)));

        st.addFunctionSymbol(new FunctionSymbol("o", C));
        st.addFunctionSymbol(new FunctionSymbol("C$$f", Sort.get("field", C, Sort.INT)));
    }

    @Test @Parameters
    public void testArithmetic(String input) throws DafnyParserException, DafnyException {

        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    public void testSubscript() throws DafnyParserException, DafnyException {

        st.addFunctionSymbol(new FunctionSymbol("idx_91", Sort.INT));
        Term parsed = TermParser.parse(st, "idx_91");
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals("idx\u2089\u2081", printed.toString());
    }

    @Test @Parameters
    public void testLogic(String input) throws DafnyParserException, DafnyException {

        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test @Parameters
    public void testWithLinebreak(String input, String expected, Integer linewidth)
             throws DafnyParserException, DafnyException {

        Term parsed = TermParser.parse(st, input);
        PrettyPrint pp = new PrettyPrint();
        AnnotatedString printed = pp.print(parsed, linewidth);

        assertEquals(expected, printed.toString());
    }

    @Test @Parameters
    public void testHeap(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    @Parameters
    public void testSpecialFunctions(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    @Parameters
    public void testADTExpressions(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    @Parameters
    public void testLetExpressions(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    @Parameters
    public void testSchemaExpressions(String input) throws Exception {
        TermParser tp = new TermParser(st);
        tp.setSchemaMode(true);
        Term parsed = tp.parse(input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    @Parameters
    public void testDafnyFunctions(String input) throws Exception {
        Project p = TestUtil.mockProject(
                "class C { function cfct(a: int, c:C) : int {1}}\n" +
                   "function fct(a: int, c: C) : bool {true}");
        st.addFunctionSymbol(new DafnyFunctionSymbol(p.getFunction("fct")));
        st.addFunctionSymbol(new DafnyFunctionSymbol(
                p.getClass("C").getFunction("cfct")));

        TermParser tp = new TermParser(st);
        Term parsed = tp.parse(input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    public void testNonFix() throws DafnyParserException, DafnyException {
        Term parsed = TermParser.parse(st, "anything(i1+1)");
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals("anything(i1 + 1)", printed.toString());
    }

    @Test
    public void testAnnotations1() throws Exception {
        st.addFunctionSymbol(new FunctionSymbol("i2", Sort.INT));
        st.addFunctionSymbol(new FunctionSymbol("i3", Sort.INT));

        Term t = TermParser.parse(st, "i1 + i2 + i3");
        AnnotatedString as = new PrettyPrint().print(t);
        assertEquals("i1 + i2 + i3", as.toString());
        assertEquals("[Element[begin=0;end=7;attr=0], " +
                "Element[begin=0;end=2;attr=0.0], " +
                "Element[begin=5;end=7;attr=0.1], " +
                "Element[begin=10;end=12;attr=1]]", as.describeAllElements());
    }

    /*
     * To fix this case, let expressions must take their
     * substitutions as subterms
     */

    @Test @Ignore
    public void testAnnotations2() throws Exception {
        Term t = TermParser.parse(st, "let var x := i1 + i1 :: (x == i1)");
        AnnotatedString as = new PrettyPrint().print(t);
        assertEquals("let x := i1 + i1 :: i1 = i1)", as.toString());
        assertEquals("[Element[begin=8;end=15;attr=1], " +
                "Element[begin=8;end=10;attr=1.0], " +
                "Element[begin=13;end=15;attr=1.1], " +
                "Element[begin=17;end=26;attr=0], " +
                "Element[begin=18;end=20;attr=0.0], " +
                "Element[begin=23;end=25;attr=0.1]]", as.describeAllElements());

    }

    @Test
    public void testAnnotations3() throws Exception {
        Term t = TermParser.parse(st, "1 + (2 + 3)");
        // 01234567890
        AnnotatedString as = new PrettyPrint().print(t);
        assertEquals("1 + (2 + 3)", as.toString());
        assertEquals("[Element[begin=0;end=1;attr=0], " +
                "Element[begin=4;end=11;attr=1], " +
                "Element[begin=5;end=6;attr=1.0], " +
                "Element[begin=9;end=10;attr=1.1]]", as.describeAllElements());
    }

    @Test
    public void testAnnotationsExtension() throws Exception {
        PrettyPrint pp = new PrettyPrint();
        String string = "{1, 2 + 2, 3}";
        Term t = TermParser.parse(st, string);
        AnnotatedString as = new PrettyPrint().print(t);
        assertEquals(string, as.toString());

        assertEquals("[Element[begin=1;end=2;attr=1.1.0], " +
                        "Element[begin=4;end=9;attr=1.0], " +
                        "Element[begin=4;end=5;attr=1.0.0], " +
                        "Element[begin=8;end=9;attr=1.0.1], " +
                        "Element[begin=11;end=12;attr=0]]", as.describeAllElements());

        for (AnnotatedString.TermElement termElement : as.getAllTermElements()) {
            Term subterm = termElement.getSubtermSelector().selectSubterm(t);
            String subtermString = pp.print(subterm).toString();
            String substring = string.substring(termElement.getBegin(), termElement.getEnd());
            assertEquals(subtermString, substring);
        }
    }

    @Test
    public void testSequent() throws TermBuildException {

        Term b1 = new ApplTerm(st.getFunctionSymbol("b1"));
        Term b2 = new ApplTerm(st.getFunctionSymbol("b2"));
        ProofFormula pf1 = new ProofFormula(b1);
        ProofFormula pf2 = new ProofFormula(b2);

        Sequent s = new Sequent(Arrays.asList(pf1, pf2), Arrays.asList(pf2, pf1));

        PrettyPrint pp = new PrettyPrint();
        String annotated = pp.print(s);
        assertEquals("b1, b2 |- b2, b1", annotated.toString());

        annotated = pp.print(s, 7);
        assertEquals(
                "   b1,\n   b2\n|- b2,\n   b1", annotated.toString());

        Sequent noAnte = new Sequent(Collections.emptyList(), Arrays.asList(pf2, pf1));
        annotated = pp.print(noAnte);
        assertEquals("|- b2, b1", annotated.toString());

        Sequent noSucc = new Sequent(Arrays.asList(pf2, pf1), Collections.emptyList());
        annotated = pp.print(noSucc);
        assertEquals("b2, b1 |-", annotated.toString());
    }
}
