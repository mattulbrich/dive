/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

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
            assertEquals(Integer.toString(i), s.getLast());
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
            assertEquals(Integer.toString(i), s2.getLast());
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

    @Test
    public void testContains() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "1", "3", "4", "5", "6"));
        assertTrue(s.contains("1"));
        assertFalse(s.contains("2"));
        assertTrue(s.contains("6"));
    }

    @Test
    public void testAppendAll() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> t = ImmutableList.from(Arrays.asList("7", "8", "9"));
        ImmutableList<String> u = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6", "7", "8", "9"));
        assertEquals(u, s.appendAll(t));

        List<String> a = Arrays.asList("7", "8", "9");
        assertEquals(u, s.appendAll(a));
    }

    @Test
    public void testFrom() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> t = ImmutableList.from("1", "2", "3", "4", "5", "6");
        assertEquals(t, s);
    }

    @Test
    public void testTakeFirstDropLast() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> ex = ImmutableList.from(Arrays.asList("1", "2"));
        assertEquals(ex, s.takeFirst(2));
        assertEquals(ex, s.dropLast(4));

        assertEquals(ImmutableList.nil(), s.takeFirst(0));
        assertEquals(ImmutableList.nil(), s.dropLast(s.size()));
    }

    @Test
    public void testSubList() {

        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> ex1 = ImmutableList.from(Arrays.asList("1", "2"));
        ImmutableList<String> ex2 = ImmutableList.from(Arrays.asList("3", "4", "5"));

        assertEquals(ex1, s.subList(0, 2));
        assertEquals(ex2, s.subList(2, 3));
        assertEquals(ImmutableList.nil(), s.subList(1, 0));

        try {
            // should throw!
            s.subList(3, -2);
            fail();
        } catch (IndexOutOfBoundsException ex) {

        }

        try {
            // should throw!
            s.subList(100, 0);
            fail();
        } catch (IndexOutOfBoundsException ex) {

        }
    }

    @Test
    public void testMap() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<Integer> t = ImmutableList.from(1, 2, 3, 4, 5, 6);
        assertEquals(t, s.map(Integer::parseInt));
    }

    @Test
    public void testFilter() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        ImmutableList<String> t = ImmutableList.from(Arrays.asList("2", "4", "6"));
        assertEquals(t, s.filter(x -> Integer.parseInt(x) % 2 == 0));
    }

    @Test
    public void testFindFirst() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        assertEquals("2", s.findFirst(x -> Integer.parseInt(x) % 2 == 0));
    }

    @Test
    public void testEquals() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4"));
        ImmutableList<String> s2 = ImmutableList.from(Arrays.asList("1", "2", "3", "4"));
        ImmutableList<String> t = ImmutableList.from(Arrays.asList("1", "2", "3"));

        assertTrue(s.equals(s2));
        assertFalse(s.equals(t));
        assertFalse(t.equals(s));
    }

    @Test
    public void testSort() {
        ImmutableList<String> s = ImmutableList.nil();
        assertEquals(s, s.sort());

        s = ImmutableList.from("1", "2", "3");
        assertEquals(s, s.sort());

        s = ImmutableList.from(Arrays.asList("D", "C", "B"));
        ImmutableList<String> t = ImmutableList.from(Arrays.asList("B", "C", "D"));
        assertEquals(t, s.sort());
    }

    @Test
    public void testWithoutDuplicates() {
        ImmutableList<Integer> s = ImmutableList.from(1,2,3,4,5);
        assertSame(s, s.withoutDuplicates());

        ImmutableList<Integer> s2 = ImmutableList.from(1,2,3,2,4,2,5);
        ImmutableList<Integer> s2_ex = ImmutableList.from(1,2,3,4,5);
        assertEquals(s2_ex, s2.withoutDuplicates());

        ImmutableList<Integer> s3 = ImmutableList.from(Collections.nCopies(100, 42));
        ImmutableList<Integer> s3_ex = ImmutableList.single(42);
        assertEquals(s3_ex, s3.withoutDuplicates());
    }
}
