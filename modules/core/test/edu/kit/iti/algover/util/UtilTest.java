/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;

import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class UtilTest {

    public static String[] parametersForTestMaskFileName() {
        return new String[]{
                "abcdefg, abcdefg",
                "Class/while_true/POST[label2], Class+while_true+POST[label2]",
                "Class/while_true/POST[label-3], Class+while_true+POST[label%2d3]",
                "C/if_true/POST[with spaces], C+if_true+POST[with-spaces]",
        };
    }

    @Test
    public void testReadOnlyArrayListEArray() {

        String[] array = "Some words in an array".split(" ");
        List<String> list = Util.readOnlyArrayList(array);

        assertEquals(array.length, list.size());
        assertEquals("[Some, words, in, an, array]", list.toString());
        assertTrue(Arrays.equals(array, list.toArray(new String[0])));

    }

    @Test
    @Parameters
    public void testMaskFileName(String filename, String expected) {
        assertEquals(expected, Util.maskFileName(filename));
    }

    @Test
    public void testRemoveDuplicates() {
        List<Integer> l = new ArrayList<>(Arrays.asList(1,2,3,2,3,4,1));
        Util.removeDuplicates(l);
        assertEquals(Arrays.asList(1,2,3,4), l);
    }
}
