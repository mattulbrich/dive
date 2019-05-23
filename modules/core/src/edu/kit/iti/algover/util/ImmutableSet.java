/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

public interface ImmutableSet<T> extends Iterable<T> {

    ImmutableSet<T> add(T element);

    ImmutableSet<T> addAll(Iterable<T> elements);

    boolean contains(T element);

    boolean containsAll(Iterable<T> element);

    ImmutableSet<T> remove(T element);

    ImmutableSet<T> removeAll(Iterable<? extends T> elements);

    <U, E extends Exception> ImmutableSet<U> map(FunctionWithException<T, U, E> function) throws E;

    // <E extends Exception> ImmutableSet<T> filter(FunctionWithException<T, Boolean, E> filter) throws E;

    // <E extends Exception> boolean forall(FunctionWithException<T, Boolean, E> predicate) throws E;

    <E extends Exception> boolean exists(FunctionWithException<T, Boolean, E> predicate) throws E;

}
