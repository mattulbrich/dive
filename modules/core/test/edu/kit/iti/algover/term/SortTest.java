/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import static org.junit.Assert.*;

import edu.kit.iti.algover.term.builder.TermBuildException;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;

import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class SortTest {

    private Sort CLASS_SORT = Sort.getClassSort("Demo");
    private Sort OTHER_CLASS_SORT = Sort.getClassSort("Demo2");

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    public Object[][] parametersForTestClassSorts() {
        return new Object[][] {
            { Sort.INT, false },
            { Sort.BOOL, false },
            { Sort.HEAP, false },
            { Sort.OBJECT, false },
            { Sort.NULL, false },
            { Sort.get("field", Sort.get("A"), Sort.BOOL), false },
            { Sort.get("set", Sort.INT), false },
            { Sort.get("seq", Sort.INT), false },
            { Sort.get("array", Sort.INT), false },

            { Sort.get("A"), true },
            { Sort.get("Object"), true },
        };
    }

    public Object[][] parametersForTestHierarchy() {
        return new Object[][] {
            // top, bottom, expected
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

            { Sort.BOTTOM, Sort.BOTTOM, true},
            { Sort.BOTTOM, Sort.INT, false},
            { Sort.INT, Sort.BOTTOM, true},
            { Sort.BOTTOM, CLASS_SORT, false},
            { CLASS_SORT, Sort.BOTTOM, true},
            { Sort.BOTTOM, Sort.NULL, false},
            { Sort.NULL, Sort.BOTTOM, true},
            { Sort.BOTTOM, Sort.UNTYPED_SORT, true},
            { Sort.UNTYPED_SORT, Sort.BOTTOM, false},

            { Sort.get("$tuple", CLASS_SORT, Sort.OBJECT),
              Sort.get("$tuple", CLASS_SORT, CLASS_SORT), true },
            { Sort.get("$tuple", CLASS_SORT, Sort.OBJECT),
              Sort.get("$tuple", Sort.OBJECT, CLASS_SORT), false },
            { Sort.get("$tuple", CLASS_SORT, Sort.OBJECT),
              Sort.get("$tuple", CLASS_SORT), false },
            { Sort.get("$tuple"), Sort.get("$tuple"), true },
            { Sort.get("$tuple", Sort.INT),
              Sort.get("$tuple", Sort.OBJECT), false },
        };
    }

    private static final Sort INT_ARRAY = Sort.get("array", Sort.INT);

    public Object[][] parametersForTestSupremum() {
        return new Object[][] {
            { Sort.NULL, Sort.NULL, Sort.NULL },
            { Sort.NULL, Sort.OBJECT, Sort.OBJECT },
            { CLASS_SORT, Sort.NULL, CLASS_SORT },
            { CLASS_SORT, OTHER_CLASS_SORT, Sort.OBJECT },
            { INT_ARRAY, CLASS_SORT, Sort.OBJECT },
            { INT_ARRAY, Sort.NULL, INT_ARRAY },
            { Sort.INT, Sort.OBJECT, null },
            { Sort.UNTYPED_SORT, Sort.BOTTOM, Sort.BOTTOM},
            { Sort.UNTYPED_SORT, CLASS_SORT, CLASS_SORT},
        };
    }

    public String[][] parametersForTestParse() {
        return new String[][] {
                { "int" },
                { "set<object>" },
                { "X<Y<Z,A>,Y<A,Z>>" },
                { "X<Y<Z<A<B>>>>" },
                // Was a problem
                { "field<C, int>" },
                { "X <  Y ,  Z >" },
                { "\tbool" },
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

    @Test @Parameters
    public void testClassSorts(Sort sort, boolean isClassSort) {
        assertEquals(isClassSort, sort.isClassSort());
    }

    @Test @Parameters
    public void testSupremum(Sort s1, Sort s2, Sort expected) throws TermBuildException {
        if(expected == null) {
            thrown.expect(TermBuildException.class);
            thrown.expectMessage("No common supertype for ");
        }

        Sort sup = Sort.supremum(s1, s2);
        Sort sup2 = Sort.supremum(s2, s1);

        assertEquals(expected, sup);
        assertEquals(sup, sup2);
        assertTrue(s1.isSubtypeOf(sup));
        assertTrue(s2.isSubtypeOf(sup));
    }

    @Test @Parameters
    public void testParse(String string) {
        Sort sort = Sort.parseSort(string);
        String actual = sort.toString();

        String expected = string.replaceAll("\\s+", "");

        assertEquals(expected, actual);
    }
}
