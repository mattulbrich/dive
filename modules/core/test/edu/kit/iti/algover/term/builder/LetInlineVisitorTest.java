/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.*;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.rules.SubtermSelector;
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

import java.util.IdentityHashMap;
import java.util.Map;

@RunWith(JUnitParamsRunner.class)
public class LetInlineVisitorTest {

    public String[][] parametersForTestInline() {
        return new String[][] {
            { "let x := 7 ; x+5", "7 + 5" },
            { "let x := 7 ; i+5", "i + 5" }, // revealed a bug
            { "i + (let x := 7 ; x+5)", "i + (7 + 5)" },
            { "let x:=i+1 :: let x:=x+1 :: let x:=x+1 :: x", "i+1+1+1" },
            { "let i,j := j,i :: i+j", "j+i" },
            { "let i,j := j,i :: let i,j := j,i :: i+j", "i+j" },
            { "forall x:int :: let y := 3 :: x>y", "forall x:int :: x>3" },
            { "let x := 3 :: forall x:int :: x>x", "forall x:int :: x>x" },
            { "forall x:int :: x > 0", "forall x:int :: x > 0" },
            { "let x := 0 :: let x := x + 1 :: let x := x + 1 :: x > 0",
              "0+1+1 > 0"},
            { "let x := 0 :: let x := x + 1 :: forall x :: let x := x + 1 :: x > 0",
              "forall x :: x+1 > 0"},
        };
    }

    @Test @Parameters
    public void testInline(String input, String expected) throws Exception {
        BuiltinSymbols s = new BuiltinSymbols();
        s.addFunctionSymbol(new FunctionSymbol("i", Sort.INT));
        s.addFunctionSymbol(new FunctionSymbol("j", Sort.INT));

        Term inputTerm = TermParser.parse(s, input);
        Term expectTerm = TermParser.parse(s, expected);

        Term inlined =  LetInlineVisitor.inline(inputTerm);

        assertEquals(expectTerm, inlined);
    }

    @Test
    public void testMapUpdate() throws Exception {
        BuiltinSymbols s = new BuiltinSymbols();

        Term inputTerm = TermParser.parse(s, "let i := 1 :: let j,k := 2,3 :: (0+i)+(j+(let a:=3 :: a))");
        Term expectTerm = TermParser.parse(s, "(0+1)+(2+3)");

        Map<Term, SubtermSelector> map = new IdentityHashMap<>();
        addToMap(map, inputTerm, new SubtermSelector());

        Term inlined = LetInlineVisitor.inline(map, inputTerm);
        assertEquals(expectTerm, inlined);

        assertEquals(new SubtermSelector(0, 0), map.get(inlined));
        assertEquals(new SubtermSelector(0, 0, 1), map.get(inlined.getTerm(1)));
    }

    private void addToMap(Map<Term, SubtermSelector> map, Term t, SubtermSelector subtermSelector) {
        map.put(t, subtermSelector);
        for (int i = 0; i < t.countTerms(); i++) {
            addToMap(map, t.getTerm(i), new SubtermSelector(subtermSelector, i));
        }
    }

}
