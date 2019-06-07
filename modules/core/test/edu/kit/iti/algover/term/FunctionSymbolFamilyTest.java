/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import static edu.kit.iti.algover.term.FunctionSymbolFamily.VAR1;
import static edu.kit.iti.algover.term.FunctionSymbolFamily.VAR2;
import static org.junit.Assert.assertEquals;

import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;

import edu.kit.iti.algover.data.BuiltinSymbols;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class FunctionSymbolFamilyTest {

    public String[][] parametersForTestParseSortParameters() {
        return new String[][] {
            { "A<B>", "[B]" },
            { "A<B<C<D>>,E<F,G,H<J>>>", "[B<C<D>>, E<F,G,H<J>>]" },
            { "A<B,C,D,E,F>", "[B, C, D, E, F]" },
            { "Longer<Names,Are,Supported0_123$y>", "[Names, Are, Supported0_123$y]" },
            { "NoArgs", "[]" },
            // Missing closing delimiters are just assumed
            { "A<B", "[B]" },
            { "A<B,C", "[B, C]" },
        };
    }


    @Test
    public void testInstantiate() {

        Sort p2 = Sort.get("p2", VAR1, VAR2);
        Sort nested = Sort.get("n", Sort.get("n2", VAR1));

        FunctionSymbolFamily fsf =
                new FunctionSymbolFamily(
                        new FunctionSymbol("test", p2, p2, nested), 2);

        FunctionSymbol result = fsf.instantiate(Sort.INT, Sort.BOOL);

        assertEquals("test<int,bool>(p2<int,bool>, n<n2<int>>) : p2<int,bool>",
                result.toString());
    }

    // from a bug
    @Test
    public void testSelect() {
        FunctionSymbol sel = BuiltinSymbols.SELECT.instantiate(Sort.getClassSort("C"), Sort.INT);
        assertEquals("$select<C,int>(heap, C, field<C,int>) : int", sel.toString());
    }

    @Test @Parameters
    public void testParseSortParameters(String input, String expected) {
        List<Sort> result = FunctionSymbolFamily.parseSortParameters(input);
        assertEquals(input, expected, result.toString());
    }

}
