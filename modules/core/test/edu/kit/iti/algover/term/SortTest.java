/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import static org.junit.Assert.*;

import org.junit.Test;

public class SortTest {

    @Test
    // revealed a bug
    public void testConstructor() {
        Sort s = new Sort("test");
        assertEquals("test", s.getName());
        assertEquals("[]", s.getArguments().toString());
        assertEquals("test", s.toString());

        Sort s2 = new Sort("outer", s, s);
        assertEquals("outer", s2.getName());
        assertEquals("[test, test]", s2.getArguments().toString());
        assertEquals("outer<test,test>", s2.toString());

    }

}
