/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import static org.junit.Assert.*;

import org.antlr.analysis.SemanticContext.TruePredicate;
import org.junit.Test;
import org.junit.runner.RunWith;

import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class SortTest {

    private Sort CLASS_SORT = Sort.getClassSort("Demo");

    public Object[][] parametersForTestHierarchy() {
        return new Object[][] {
            { Sort.OBJECT, Sort.NULL, true },
            { Sort.OBJECT, Sort.OBJECT, true },
            { Sort.OBJECT, CLASS_SORT, true },
            { CLASS_SORT, CLASS_SORT, true },
            { CLASS_SORT, Sort.NULL, true },
            { Sort.NULL, Sort.NULL, true },
            { Sort.NULL, Sort.OBJECT, false },

            { Sort.OBJECT, Sort.INT, false },
            { CLASS_SORT, Sort.INT, false },
            { Sort.NULL, Sort.INT, false },

            { Sort.INT, Sort.INT, true },
            { Sort.INT, Sort.NULL, false },
            { Sort.INT, Sort.OBJECT, false },
            { Sort.INT, CLASS_SORT, false },

            { Sort.OBJECT, Sort.UNTYPED_SORT, true },
            { CLASS_SORT, Sort.UNTYPED_SORT, true },
            { Sort.UNTYPED_SORT, CLASS_SORT, false },
        };
    }

    @Test
    // revealed a bug
    public void testConstructor() {
        Sort s = Sort.get("test");
        assertEquals("test", s.getName());
        assertEquals("[]", s.getArguments().toString());
        assertEquals("test", s.toString());

        Sort s2 = Sort.get("outer", s, s);
        assertEquals("outer", s2.getName());
        assertEquals("[test, test]", s2.getArguments().toString());
        assertEquals("outer<test,test>", s2.toString());

    }

    @Test @Parameters
    public void testHierarchy(Sort top, Sort bottom, boolean expected) {

        assertEquals(expected, bottom.isSubtypeOf(top));

    }

}
