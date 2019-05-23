/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

public class ArrayUtil {

    @SuppressWarnings("unchecked")
    public static <T> T[] create(int length) {
        return (T[]) new Object[length];
    }

    public static <T> T[] singleton(T elem) {
        T[] array = create(1);
        array[0] = elem;
        return array;
    }

    public static <T> T[] prepend(T elem, T[] array) {
        T[] longArray = create(array.length + 1);
        longArray[0] = elem;
        for (int i = 0; i < array.length; i++) {
            longArray[i + 1] = array[i];
        }
        return longArray;
    }

}
