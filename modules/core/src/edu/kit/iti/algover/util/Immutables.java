/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;

public class Immutables {

    public static <K,V> ImmutableMap<K,V> emptyMap() {
        return ImmutableLinearMap.emptyMap();
    }

    public static <T> ImmutableSet<T> emptySet() {
        return ImmutableLinearSet.emptySet();
    }

    @SuppressWarnings("unchecked")
    public static <T> ImmutableSet<T> setOf(T... elements) {
        return ImmutableLinearSet.from(elements);
    }
}
