/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import java.util.NoSuchElementException;

public final class ExcusableValue<A, Ex extends Exception> {

    private final A value;
    private Ex excuse;

    private ExcusableValue(A value, Ex excuse) {
        assert (value == null) != (excuse == null);
        this.value = value;
        this.excuse = excuse;
    }

    public static <A, Ex extends Exception> ExcusableValue<A, Ex> value(A value) {
        return new ExcusableValue<>(value, null);
    }

    public static <A, Ex extends Exception> ExcusableValue<A, Ex> excuse(Ex excuse) {
        return new ExcusableValue<>(null, excuse);
    }

    /**
     * Precondition: this.hasValue() == true.
     * @return
     * @throws NoSuchElementException if no value present.
     */
    public A get() {
        if (value == null) {
            throw new NoSuchElementException();
        } else {
            return value;
        }
    }

    public Ex getExcuse() {
        if (excuse == null) {
            throw new NoSuchElementException();
        } else {
            return excuse;
        }
    }

    public A getOrThrow() throws Ex {
        throwIfExcused();
        return get();
    }

    /**
     * precondition: hasValue() == false
     * @return
     */
    public String getExcuseMessage() {
        if (excuse == null) {
            throw new NoSuchElementException();
        } else {
            return excuse.getMessage();
        }
    }

    public boolean hasValue() {
        return value != null;
    }

    // Feel free to add any convenience method from java.util.Optional or from

    // anywhere else.

    /**
     * If a value is present, performs the given action with the value,
     * otherwise does nothing.
     *
     * @param action the action to be performed, if a value is present
     * @throws NullPointerException if value is present and the given action is
     *         {@code null}
     */
    public <Ex extends Exception> void ifPresent(ConsumerWithException<? super A, Ex> action) throws Ex {
        if (value != null) {
            action.accept(value);
        }
    }

    /**
     * If a value is present, return a new value after applying the map.
     * If there is a excuse, return that.
     *
     * @param map the action to be performed, if a value is present
     * @throws NullPointerException if value is present and the given action is
     *         {@code null}
     */
    public <B, E extends Exception> ExcusableValue<B, Ex> map(FunctionWithException<? super A, B, E> map) throws E {
        if (value != null) {
            return ExcusableValue.value(map.apply(value));
        } else {
            // One could reuse "this" but that would be far from typesafe.
            return ExcusableValue.excuse(getExcuse());
        }
    }

    public<B, E extends Exception> ExcusableValue<B, Ex> flatMap(FunctionWithException<? super A, ExcusableValue<B, Ex>, E> map) throws E {
        if (value != null) {
            return map.apply(value);
        } else {
            // One could reuse "this" but that would be far from typesafe.
            return ExcusableValue.excuse(getExcuse());
        }
    }

    public void throwIfExcused() throws Ex {
        if (!hasValue()) {
            throw excuse;
        }
    }

    public A getOrElse(A alternativeValue) {
        if (hasValue()) {
            return value;
        } else {
            return alternativeValue;
        }
    }
}
