/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Properties;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

import static org.junit.Assert.*;

@RunWith(Parameterized.class)
public class TermParserTest {

    private static SymbolTable symbolTable;

    private final String input;
    private final String expected;

    private String name;

    public TermParserTest(String name, String input, String expected) {
        this.name = name;
        this.input = input;
        this.expected = expected;
    }

    @Parameters(name = "{0}")
    public static Iterable<Object[]> data() throws Exception {

        Properties p = new Properties();
        p.loadFromXML(TermParserTest.class.getResourceAsStream("termParser.xml"));

        List<Object[]> result = new ArrayList<>();

        for(Entry<Object, Object> en : p.entrySet()) {
            String name = en.getKey().toString();
            String[] parts = en.getValue().toString().split("###");
            result.add(new Object[] { name, parts[0].trim(), parts[1].trim() });
        }

        return result;
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

    @Test
    public void test() throws DafnyParserException {
        Term term = TermParser.parse(symbolTable, input);
        String actual = term.toString();

        assertEquals(name, expected, actual);
    }

}
