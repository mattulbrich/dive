/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class ReplaceVisitorTest {

    private MapSymbolTable symbTable;

    public String[][] parametersForTestReplace() {
        return new String[][] {
            { "(1 + (2 - 1)) * 3", "0.1.1", "4", "(1 + (2 - 4)) * 3" },
            { "f(1,2,3,4,5)", "2", "33", "f(1,2,33,4,5)" },
            { "forall x:int :: x>7", "0.1", "8", "forall x:int :: x > 8" },
            { "22 > 11", "", "true", "true" },
            { "c2 == c", "1", "null", "c2 == null" },
            { "c2 == null", "1", "c", "c2 == c" },
            { "let i := 5 :: i + 1 > 0", "1", "4", "let i := 4 :: i + 1 > 0" }
        };

    }

    public String[][] parametersForTestFail() {
        return new String[][] {
            { "1+2", "1", "true", "Unexpected argument sort for argument 2" },
        };
    }

    @Test @Parameters
    public void testReplace(String in, String select, String replace, String expect) throws Exception {

        Term inTerm = TermParser.parse(symbTable, in);
        Term replaceTerm = TermParser.parse(symbTable, replace);
        SubtermSelector subsel = new SubtermSelector(select);
        Term expectTerm = TermParser.parse(symbTable, expect);

        Term result = ReplaceVisitor.replace(inTerm, subsel, replaceTerm);
        assertEquals(in, expectTerm, result);
    }

    @Test @Parameters
    public void testFail(String in, String select, String replace, String expect) {
        try {
            Term inTerm = TermParser.parse(symbTable, in);
            Term replaceTerm = TermParser.parse(symbTable, replace);
            SubtermSelector subsel = new SubtermSelector(select);

            Term result = ReplaceVisitor.replace(inTerm, subsel, replaceTerm);
            System.out.println(result);
        } catch(Exception ex) {
            ex.printStackTrace();
            assertTrue(ex.getMessage().contains(expect));
        }
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("f", Sort.INT, Sort.INT, Sort.INT, Sort.INT, Sort.INT ,Sort.INT));
        map.add(new FunctionSymbol("c", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("c2", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("i", Sort.INT));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }
}
