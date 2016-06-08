/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Iterator;

import org.junit.Test;

public class TestImmutableList {

    @Test
    public void testGet() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        for (int i = 0; i < s.size(); i++) {
            assertEquals(Integer.toString(i+1), s.get(i));
        }
    }

    @Test
    public void testToString() throws Exception {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        assertEquals("[1, 2, 3, 4, 5, 6]", s.toString());
    }


    @Test
    public void testFromArray() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        for(int i = 6; i >= 1; i--) {
            assertEquals(Integer.toString(i), s.getHead());
            s = s.getTail();
        }
    }

    @Test
    public void testReverse() throws Exception {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> s2 = s.reverse();
        ImmutableList<String> s3 = s.reverse().reverse();

        assertEquals(s, s3);

        for(int i = 1; i <= 6; i++) {
            assertEquals(Integer.toString(i), s2.getHead());
            s2 = s2.getTail();
        }
    }

    @Test
    public void testAppend() throws Exception {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> s2 = s.append("7");
        s2 = s2.append("8");
        assertEqualIterators(Arrays.asList("1 2 3 4 5 6 7 8".split(" ")).iterator(), s2.iterator());
    }

    private void assertEqualIterators(Iterator<?> it1, Iterator<?> it2) {
        while(it1.hasNext() && it2.hasNext()) {
            assertEquals(it1.next(), it2.next());
        }
        assertTrue(it1.hasNext() == it2.hasNext());
    }

    @Test
    public void testAsCollection() throws Exception {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        assertEqualIterators(s.iterator(), s.asCollection().iterator());
    }
}
