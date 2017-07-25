/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class PrettyPrintTest {

    private SymbolTable st;

    public String[][] parametersForTestArithmetic() {
        return new String[][] {
            { "1 + 2" },
            { "1 + i1" },
            { "1 + (2 + 3)" },
            { "1 + 2 + 3" },
            { "1 + 2 - 3" },
            { "1 + 2 * 3" },
            { "1 * 2 + 3" },
            { "(1 + 2) * 3" },
            { "1 * (2 + 3)" },
            { "1 < 2" },
            { "1 <= 2" },
            { "1 > 0" },
            { "1 >= 0" },
            { "1 + 2 >= 1 * 1" },
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
        };
    }

    public String[][] parametersForTestSpecialFunctions() {
        return new String[][] {
            { "if i1 == 0 then i1 else 0" },
            { "i1 + (if i1 == 0 then i1 else 0)" },
            { "if b1 then let x := 0 :: x + 1 else if b1 then 0 else 1" }, // revealed a bug
        };
    }

    public String[][] parametersForTestHeap() {
        return new String[][] {
            { "o.f" },
            { "heap[o.f := 4][o.f := 5][anon(someset, h_2)]" },
            { "o.f @ h_2" },
            { "o.f @ heap[o.f := 3]" },
            { "let o.f := 4 :: o.f + 2" },
        };
    }

    public String[][] parametersForTestLetExpressions() {
        return new String[][] {
            { "let x := 0 :: x * 2" },
            { "1 + (let x := 0 :: x * 2)" },
            { "(let x := 0 :: x * 2) + 1" },
            { "let x := 0 :: let y := 0 :: x * y" },
            { "let x := 0 :: (let y := 0 :: x * y) * x" },
            { "let x, y := 1, 2 :: x + y" },  // revealed a bug
            { "let x := 0 :: if b1 then x else 0" },
            { "1 + (let x := 0 :: if b1 then x else 0)" }, // revealed a bug
        };
    }


    @Before
    public void setupTable() {
        st = new BuiltinSymbols();
        st.addFunctionSymbol(new FunctionSymbol("i1", Sort.INT));
        st.addFunctionSymbol(new FunctionSymbol("b1", Sort.BOOL));
        st.addFunctionSymbol(new FunctionSymbol("anything", Sort.INT, Sort.INT));
    }

    @Test @Parameters
    public void testArithmetic(String input) throws DafnyParserException {

        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test @Parameters
    public void testLogic(String input) throws DafnyParserException {

        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test @Parameters @Ignore
    public void testHeap(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test @Parameters
    public void testSpecialFunctions(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test @Parameters
    public void testLetExpressions(String input) throws Exception {
        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    public void testNonFix() throws DafnyParserException {
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

}
