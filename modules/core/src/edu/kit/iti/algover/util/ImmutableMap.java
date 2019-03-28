/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import java.util.Map;

public interface ImmutableMap<K, V> {
    ImmutableLinearMap<K, V> put(K key, V value);

    boolean containsKey(K key);

    V get(K key);

    ImmutableLinearMap<K, V> removeKey(K key);

    ImmutableLinearMap<K, V> putAll(Map<K, V> map);
}
