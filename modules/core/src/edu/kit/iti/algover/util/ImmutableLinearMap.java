/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;

public class ImmutableLinearMap<K, V> implements ImmutableMap<K, V> {

    private static final Object REMOVED_INDICATOR = new Object();

    @SuppressWarnings({"unchecked", "rawtypes"})
    private static final ImmutableLinearMap EMPTY = new ImmutableLinearMap(ImmutableList.nil());

    private final ImmutableList<Pair<K, V>> data;

    private ImmutableLinearMap(ImmutableList<Pair<K, V>> list) {
        this.data = list;
    }

    @Override
    public ImmutableLinearMap<K, V> put(K key, V value) {
        Objects.nonNull(key);
        return new ImmutableLinearMap<K, V>(data.append(new Pair<>(key, value)));
    }

    @Override
    public boolean containsKey(K key) {
        Pair<K, V> element = data.findLast(p -> p.fst.equals(key));
        return element != null && element.snd != removedIndicator();
    }

    @Override
    public V get(K key) {
        Pair<K, V> element = data.findLast(p -> p.fst.equals(key));
        if(element != null) {

            V v = element.snd;
            if(v != removedIndicator()) {
                return v;
            }
        }
        return null;
    }

    @Override
    public ImmutableLinearMap<K, V> removeKey(K key) {
        if(!containsKey(key)) {
            return this;
        } else {
            return put(key, removedIndicator());
        }
    }

    @SuppressWarnings("unchecked")
    private V removedIndicator() {
        return (V)REMOVED_INDICATOR;
    }

    @SuppressWarnings("unchecked")
    public static <K, V> ImmutableLinearMap<K, V> emptyMap() {
        return EMPTY;
    }

    // Convenience methods

    public static <K,V> ImmutableLinearMap<K,V> single(K key, V value) {
        return ImmutableLinearMap.<K,V>emptyMap().put(key, value);
    }

    @Override
    public ImmutableLinearMap<K,V> putAll(Map<K, V> map) {
        ImmutableLinearMap<K, V> result = this;
        for (Map.Entry<K, V> entry : map.entrySet()) {
            result = result.put(entry.getKey(), entry.getValue());
        }
        return result;
    }

    @Override
    public V getOrDefault(K key, V defaultVal) {
        V result = get(key);
        if (result == null) {
            return defaultVal;
        } else {
            return result;
        }
    }

    public static <K,V> ImmutableLinearMap<K,V> from(Map<K,V> map) {
        return ImmutableLinearMap.<K,V>emptyMap().putAll(map);
    }
}
