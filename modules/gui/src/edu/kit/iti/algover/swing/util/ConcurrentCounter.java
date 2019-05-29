/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.IntConsumer;

public class ConcurrentCounter {

    private AtomicInteger counter = new AtomicInteger();
    private List<IntConsumer> listeners = new ArrayList<>();

    public void addListener(IntConsumer listener) {
        listeners.add(listener);
    }

    public void increment() {
        int v = counter.incrementAndGet();
        for (IntConsumer listener : listeners) {
            listener.accept(v);
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ConcurrentCounter that = (ConcurrentCounter) o;
        return Objects.equals(counter, that.counter) &&
                Objects.equals(listeners, that.listeners);
    }

    @Override
    public int hashCode() {
        return Objects.hash(counter, listeners);
    }

    @Override
    public String toString() {
        return "ConcurrentCounter{" + counter.get() + '}';
    }
}
