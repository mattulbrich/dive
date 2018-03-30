/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.AbstractMap;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

public class HistoryMap<K, V> extends AbstractMap<K, V> {

    private final Map<K, V> map;
    private final Stack<Pair<K, V>> undoHistory;

    public HistoryMap(Map<K, V> map) {
        this.map = map;
        this.undoHistory = new Stack<>();
    }

    @Override
    public Set<java.util.Map.Entry<K, V>> entrySet() {
        return map.entrySet();
    }

    @Override
    public V put(K key, V value) {
        undoHistory.push(new Pair<>(key, map.get(key)));
        return map.put(key, value);
    }

    public int getHistory() {
        return undoHistory.size();
    }

    public void rewindHistory(int targetSize) {
        if(targetSize < 0 || targetSize > getHistory()) {
            throw new IllegalArgumentException("Cannot rewind to " + targetSize +
                    " from state " + getHistory());
        }

        while(getHistory() > targetSize) {
            Pair<K, V> entry = undoHistory.pop();
            if(entry.snd == null) {
                map.remove(entry.fst);
            } else {
                map.put(entry.fst, entry.snd);
            }
        }
    }

    public void pop() {
        rewindHistory(getHistory()-1);
    }

    public V peek() {
        Pair<K, V> top = undoHistory.peek();
        return get(top.fst);
    }
}
