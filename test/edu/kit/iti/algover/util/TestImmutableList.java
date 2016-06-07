/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;

import org.junit.Test;

public class TestImmutableList {

    @Test
    public void testGet() {
        ImmutableList<String> s = ImmutableList.from(Arrays.asList("1", "2", "3", "4", "5", "6"));
        for (int i = 0; i < s.size(); i++) {
            assertEquals(Integer.toString(i+1), s.get(i));
        }
    }

}
