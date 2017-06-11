/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.parser;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

import static org.junit.Assert.*;

@RunWith(JUnitParamsRunner.class)
public class TermParserTest {

    private static SymbolTable symbolTable;

    public String[][] parametersForTestParsing() {
        return new String[][] {
            { "i1 + i2", "$plus(i1, i2)" },
            { "forall i: int :: 0 < i ==> i > 0",
              "(forall i:int :: $imp($lt(0, i), $gt(i, 0)))" },
            { "let var x := i1+5 ; x*2",
              "(let x := $plus(i1, 5) :: $times(x, 2))" },
        };
    }

    public String[] parametersForTestParsingIdentity() {
        return new String[] {
                "$plus(i1, i2)",
        };
    }


    @BeforeClass
    public static void setupSymbolTable() {
        symbolTable = new BuiltinSymbols();
        symbolTable.addFunctionSymbol(new FunctionSymbol("fint_int", Sort.INT, Sort.INT));
        symbolTable.addFunctionSymbol(new FunctionSymbol("fint_bool", Sort.BOOL, Sort.INT));
        symbolTable.addFunctionSymbol(new FunctionSymbol("i1", Sort.INT));
        symbolTable.addFunctionSymbol(new FunctionSymbol("i2", Sort.INT));
    }

    @AfterClass
    public static void clearSymbolTable() {
        symbolTable = null;
    }

    @Test @Parameters
    public void testParsing(String input, String expected) throws DafnyParserException {
        Term term = TermParser.parse(symbolTable, input);
        String actual = term.toString();

        assertEquals(expected, actual);
    }

    @Test @Parameters
    public void testParsingIdentity(String input) throws DafnyParserException {
        Term term = TermParser.parse(symbolTable, input);
        String actual = term.toString();

        assertEquals(input, actual);
    }
}
