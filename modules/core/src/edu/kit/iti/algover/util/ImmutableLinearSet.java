/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.Iterator;
import java.util.List;

public class ImmutableLinearSet<T> implements ImmutableSet<T> {

    private static final ImmutableLinearSet<?> EMPTY_SET =
            new ImmutableLinearSet<Object>(ImmutableList.nil());

    private final ImmutableList<T> data;

    /*@ requires: data has no doubles */
    private ImmutableLinearSet(ImmutableList<T> data) {
        if (data.size() > 50) {
            // DEBUGGING ONLY!
            System.out.println("Immutable set of size " + data.size());
        }
        this.data = data;
    }

    @SuppressWarnings("unchecked")
    public static <T> ImmutableSet<T> emptySet() {
        return (ImmutableSet<T>) EMPTY_SET;
    }

    @SuppressWarnings("unchecked")
    public static <T> ImmutableSet<T> from(T... elements) {
        ImmutableList<T> data = ImmutableList.from(elements);
        return new ImmutableLinearSet<T>(data.withoutDuplicates());
    }

    @Override
    public ImmutableSet<T> add(T element) {
        if (data.contains(element)) {
            return this;
        } else {
            return new ImmutableLinearSet<>(data.append(element));
        }
    }

    @Override
    public ImmutableSet<T> addAll(Iterable<T> elements) {
        ImmutableList<T> result = data;
        for (T element : elements) {
            if (!result.contains(element)) {
                result = result.append(element);
            }
        }
        return new ImmutableLinearSet<>(result);
    }

    @Override
    public boolean contains(T element) {
        return data.contains(element);
    }

    @Override
    public boolean containsAll(Iterable<T> elements) {
        for (T element : elements) {
            if (!contains(element)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public ImmutableSet<T> remove(T element) {
        return new ImmutableLinearSet<T>(data.filter(x -> !x.equals(element)));
    }

    @Override
    public ImmutableSet<T> removeAll(Iterable<? extends T> elements) {
        List<? extends T> toRemove = Util.toList(elements);
        // possibly inefficient. ...
        return new ImmutableLinearSet<T>(data.filter(x -> !toRemove.contains(x)));
    }

    @Override
    public <U, E extends Exception> ImmutableSet<U> map(FunctionWithException<T, U, E> function) throws E {
        return new ImmutableLinearSet<>(data.map(function));
    }

    @Override
    public <E extends Exception> boolean exists(FunctionWithException<T, Boolean, E> predicate) throws E {
        return data.exists(predicate);
    }

    @Override
    public Iterator<T> iterator() {
        return data.iterator();
    }
}
