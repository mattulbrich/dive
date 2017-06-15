/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.prettyprint;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
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
            { "1 + 2 * 3" },
            { "1 * 2 + 3" },
            { "(1 + 2) * 3" },
            { "1 * (2 + 3)" },
        };
    }

    @Before
    public void setupTable() {
        st = new BuiltinSymbols();
        st.addFunctionSymbol(new FunctionSymbol("i1", Sort.INT));
    }

    @Test @Parameters
    public void testArithmetic(String input) throws DafnyParserException {

        Term parsed = TermParser.parse(st, input);
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals(input, printed.toString());
    }

    @Test
    public void testNonFix() throws DafnyParserException {
        st.addFunctionSymbol(new FunctionSymbol("anything", Sort.INT, Sort.INT));
        Term parsed = TermParser.parse(st, "anything(i1+1)");
        AnnotatedString printed = new PrettyPrint().print(parsed);

        assertEquals("anything(i1 + 1)", printed.toString());
    }
}
