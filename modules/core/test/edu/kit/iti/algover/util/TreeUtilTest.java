/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import edu.kit.iti.algover.term.Sort;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Test;
import org.junit.runner.RunWith;

import static org.junit.Assert.*;

@RunWith(JUnitParamsRunner.class)
public class TreeUtilTest {

    public Object parametersForToTypeString() {
        return new String[][] {
                { "C<A,B>" }, { "set<int>" }, { "set<seq<C<A,B>>>" },
                { "C<C<A>,C<C<B>>>" }, { "int" }
        };
    }

    @Test @Parameters()
    public void toTypeString(String st) {
        Sort s = TreeUtil.parseSort(st);
        assertEquals(st, s.toString());
    }
}