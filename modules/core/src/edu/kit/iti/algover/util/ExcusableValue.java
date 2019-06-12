/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.util;

import nonnull.NonNull;
import nonnull.Nullable;

import java.util.NoSuchElementException;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * A container object which may or may not contain a non-{@code null} value.
 * If no value is present, instead an <em>excuse</em> in form of an exception is
 * stored.
 *
 * If a value is present, . If no
 * value is present, the object is considered <i>excused</i> and
 * {@link #hasValue()} returns {@code false}.
 *
 * If a value is present:
 * <ul>
 *     <li>no exception is present</li>
 *     <li>{@link #hasValue()} returns {@code true}</li>
 *     <li>{@link #get()} returns that value</li>
 *     <li>{@link #getOrThrow()} returns that value</li>
 *     <li>{@link #getOrElse(Object)} returns that value</li>
 *     <li>{@link #getExcuse()} throws a {@link NoSuchElementException}</li>
 *     <li>{@link #getExcuseMessage()} throws a {@link NoSuchElementException}</li>
 * </ul>
 *
 * If no value is present:
 * <ul>
 *     <li>an exception is present</li>
 *     <li>{@link #hasValue()} returns {@code false}</li>
 *     <li>{@link #get()} throws a {@link NoSuchElementException}</li>
 *     <li>{@link #getOrThrow()} throws the present exception</li>
 *     <li>{@link #getOrElse(Object)} returns the argument of that call</li>
 *     <li>{@link #getExcuse()} returns the present exception</li>
 *     <li>{@link #getExcuseMessage()} returns the the message of the
 *     present exception</li>
 * </ul>
 *
 * Objects of this class are immutable.
 *
 * @param <A> the value type of the object
 * @param <Ex> the exception type of the object
 *
 * @author Mattias Ulbrich
 * @see java.util.Optional
 */
public final class ExcusableValue<A, Ex extends Exception> {

    /**
     * the value that is stored.
     */
    private final @Nullable A value;

    /**
     * the stored exception.
     */
    private final @Nullable Ex excuse;

    //@ invariant (value == null) != (excuse == null);

    /*
     * Create a new instance.
     */
    private ExcusableValue(A value, Ex excuse) {
        assert (value == null) != (excuse == null);
        this.value = value;
        this.excuse = excuse;
    }

    /**
     * Create an excusable value that actually contains a value
     *
     * @param value non-null value to be contained
     * @param <A> the value type of the result
     * @param <Ex> the exception type of the result
     * @return a freshly created excusable value capturing {@code value}.
     */
    public static @NonNull <A, Ex extends Exception>
                ExcusableValue<A, Ex> value(@NonNull A value) {
        return new ExcusableValue<>(value, null);
    }

    /**
     * Create an excused instance that does not have a value, but an exception.
     *
     * @param excuse the non-null exception to be stored
     * @param <A> the value type of the result
     * @param <Ex> the exception type of the result
     * @return a freshly created excusable excused by {@code excuse}.
     */
    public static @NonNull <A, Ex extends Exception>
                ExcusableValue<A, Ex> excuse(Ex excuse) {
        return new ExcusableValue<>(null, excuse);
    }

    /**
     * Get the value in this object.
     *
     * <p><em>Precondition</em>: {@code this.hasValue() == true}.
     *
     * @return the value stored in this container.
     * @throws NoSuchElementException if no value present.
     */
    public A get() {
        if (value == null) {
            throw new NoSuchElementException();
        } else {
            return value;
        }
    }

    /**
     * Get the excuse in this object.
     *
     * <p><em>Precondition</em>: {@code this.hasValue() == false}.
     *
     * @return the excuse stored in this container.
     * @throws NoSuchElementException if a value and no excuse present.
     */
    public Ex getExcuse() {
        if (excuse == null) {
            throw new NoSuchElementException();
        } else {
            return excuse;
        }
    }

    /**
     * Get the value in this object, or throw the excuse.
     *
     * @return the value stored in this container.
     * @throws Ex the stored excuse thrown if present
     */
    public A getOrThrow() throws Ex {
        throwIfExcused();
        return value;
    }

    /**
     * Get the message of the excuse in this object.
     *
     * <p><em>Precondition</em>: {@code this.hasValue() == false}.
     *
     * @return the message of the excuse stored in this container.
     * @throws NoSuchElementException if a value and no excuse present.
     */
    public String getExcuseMessage() {
        if (excuse == null) {
            throw new NoSuchElementException();
        } else {
            return excuse.getMessage();
        }
    }

    /**
     * Checks if this object has a value present
     * @return true iff a value has been set at creation time.
     */
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
     * @see java.util.Optional#ifPresent(Consumer)
     */
    public <Ex extends Exception> void ifPresent(ConsumerWithException<? super A, Ex> action) throws Ex {
        if (value != null) {
            action.accept(value);
        }
    }

    /**
     * If a value is present, return a new excusable value containing the result
     * of applying the map. If there is a excuse, return an object having that.
     *
     * @param map the action to be performed, if a value is present
     * @return an {@code ExcusableValue} describing the result of applying a mapping
     *         function to the value of this object if a value is
     *         present, otherwise an excusable value with the same excuse as this.
     * @throws NullPointerException if value is present and the given action is
     *                              {@code null}
     * @see java.util.Optional#map(Function)
     */
    public <B, E extends Exception> ExcusableValue<B, Ex> map(FunctionWithException<? super A, B, E> map) throws E {
        if (value != null) {
            return ExcusableValue.value(map.apply(value));
        } else {
            // One could reuse "this" but that would be far from typesafe.
            return ExcusableValue.excuse(getExcuse());
        }
    }

    /**
     * If a value is present, return the result of applying the mappting to the
     * value. If there is a excuse, return an object having that.
     *
     * @param map the action to be performed, if a value is present
     * @return an {@code ExcusableValue} describing the result of applying a
     * mapping function to the value of this object if a value is present,
     * otherwise an excusable value with the same excuse as this.
     * @throws NullPointerException if value is present and the given action is
     *                              {@code null}
     * @see java.util.Optional#flatMap(Function)
     */
    public<B, E extends Exception> ExcusableValue<B, Ex> flatMap(FunctionWithException<? super A, ExcusableValue<B, Ex>, E> map) throws E {
        if (value != null) {
            return map.apply(value);
        } else {
            // One could reuse "this" but that would be far from typesafe.
            return ExcusableValue.excuse(getExcuse());
        }
    }

    /**
     * Throw the stored exception if there is no value (but an excuse).
     *
     * @throws Ex throws the excuse if no value present.
     */
    public void throwIfExcused() throws Ex {
        if (!hasValue()) {
            throw excuse;
        }
    }

    /**
     * Gets the stored value (if present) or the alternative value if excused.
     *
     * @param alternativeValue the value to be returned if excused.
     * @return either {@code this} or {@code alternativeValue}
     */
    public A getOrElse(A alternativeValue) {
        if (hasValue()) {
            return value;
        } else {
            return alternativeValue;
        }
    }
}
