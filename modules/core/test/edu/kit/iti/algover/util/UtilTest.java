/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.List;

import org.junit.Test;

public class UtilTest {

    @Test
    public void testReadOnlyArrayListEArray() {

        String[] array = "Some words in an array".split(" ");
        List<String> list = Util.readOnlyArrayList(array);

        assertEquals(array.length, list.size());
        assertEquals("[Some, words, in, an, array]", list.toString());
        assertTrue(Arrays.equals(array, list.toArray(new String[0])));

    }


}
