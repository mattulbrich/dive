/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import static org.junit.Assert.*;

import org.junit.Test;
import edu.kit.iti.algover.data.BuiltinSymbols;

import static edu.kit.iti.algover.term.FunctionSymbolFamily.*;

public class FunctionSymbolFamilyTest {

    @Test
    public void testInstantiate() {

        Sort p2 = Sort.get("p2", VAR1, VAR2);
        Sort nested = Sort.get("n", Sort.get("n2", VAR1));

        FunctionSymbolFamily fsf =
                new FunctionSymbolFamily(
                        new FunctionSymbol("test", p2, p2, nested), 2);

        FunctionSymbol result = fsf.instantiate(Sort.INT, Sort.BOOL);

        assertEquals("test[int,bool](p2<int,bool>, n<n2<int>>) : p2<int,bool>",
                result.toString());
    }

    // from a bug
    @Test
    public void testSelect() {
        FunctionSymbol sel = BuiltinSymbols.SELECT.instantiate(Sort.getClassSort("C"), Sort.INT);
        assertEquals("$select[C,int](heap, C, field<C,int>) : int", sel.toString());
    }

}
