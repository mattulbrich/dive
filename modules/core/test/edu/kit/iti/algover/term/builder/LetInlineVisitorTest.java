/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.*;

import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class LetInlineVisitorTest {

    public String[][] parametersForTest() {
        return new String[][] {
            { "let x := 7 ; x+5", "7 + 5" },
            { "let x := 7 ; i+5", "i + 5" }, // revealed a bug
            { "i + (let x := 7 ; x+5)", "i + (7 + 5)" },
            { "let x:=i+1 :: let x:=x+1 :: let x:=x+1 :: x", "i+1+1+1" },
            { "let i,j := j,i :: i+j", "j+i" },
            { "let i,j := j,i :: let i,j := j,i :: i+j", "i+j" },
            { "forall x:int :: let y := 3 :: x>y", "forall x:int :: x>3" },
            { "forall x:int :: x > 0", "forall x:int :: x > 0" },
        };
    }

    @Test @Parameters
    public void test(String input, String expected) throws Exception {
        BuiltinSymbols s = new BuiltinSymbols();
        s.addFunctionSymbol(new FunctionSymbol("i", Sort.INT));
        s.addFunctionSymbol(new FunctionSymbol("j", Sort.INT));

        Term inputTerm = TermParser.parse(s, input);
        Term expectTerm = TermParser.parse(s, expected);

        Term inlined =  LetInlineVisitor.inline(inputTerm);

        assertEquals(expectTerm, inlined);
    }

}
