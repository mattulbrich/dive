/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import nonnull.NonNull;
import nonnull.Nullable;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

/**
 * The Class Parameters is used to provide arguments to
 * {@link ProofRuleApplication}s.
 * <p>
 * It is essentially a map from names (Strings) to typed values
 * {@link TypedValue}.
 * <p>
 * A parameters object can be set immutable ({@link #setImmutable()}). Thus its
 * state cannot be modified any more and the object can be embedded into an
 * immutable data structure. Method {@link #isMutable()} can be used to check if
 * an object is still mutable.
 *
 * @author mulbrich
 */
public class Parameters {

    /**
     * This constant EMPTY_PARAMETERS can be used whenever "no parameters" are
     * required. It is an immutable object.
     */
    public final static Parameters EMPTY_PARAMETERS = new Parameters();

    static {
        EMPTY_PARAMETERS.setImmutable();
    }

    /**
     * The storage mapping variable names to typed values.
     */
    private final Map<String, TypedValue<?>> valueMap;
    /**
     * The mutability flag. Can never be set back to true once set to false.
     */
    private boolean mutable = true;

    /**
     * Instantiates a new empty parameter mapping.
     */
    public Parameters() {
        this.valueMap = new HashMap<>();
    }

    /**
     * Instantiates a new parameter mapping from another mapping.
     * <p>
     * It copies all entries from the argument.
     * The created object is is immutable.
     *
     * @param parameters the parameters to clone
     */
    public Parameters(@NonNull Parameters parameters) {
        this.valueMap = new HashMap<>(parameters.valueMap);
    }

    /**
     * Gets a value from the mapping.
     *
     * @param key the key to look up
     * @return the value stored for that variable, <code>null</code> if no such
     * value
     */
    public
    @Nullable
    TypedValue<?> getValue(@NonNull String key) {
        return valueMap.get(key);
    }

    /**
     * Put a value into the mapping for a variable.
     *
     * @param key   the variable name
     * @param value the value to store.
     */
    public void putValue(@NonNull String key, @NonNull TypedValue<?> value) {
        if (!isMutable()) {
            throw new IllegalStateException("These parameters are immutable");
        }
        valueMap.put(key, value);
    }

    /**
     * Checks if this object mutable.
     *
     * @return <code>true</code> iff is mutable
     */
    public boolean isMutable() {
        return mutable;
    }

    /**
     * Sets this oject to immutable. Cannot be made mutable again.
     */
    public void setImmutable() {
        mutable = false;
    }

    /**
     * Entry set for enumeration.
     *
     * @return the immutable set of entries to the object.
     */
    public Set<Entry<String, TypedValue<?>>> entrySet() {
        return valueMap.entrySet();
    }

    /**
     * The Class TypedValue captures a value together with its target type.
     * This class is not mutable.
     * <p>
     * Use {@link #set(E value)} to obtain a new {@link TypedValue} with
     * a modified value.
     *
     * @param <E> the element type
     */
    public static final class TypedValue<E> {

        /**
         * The type object as its {@link Class} object.
         */
        private
        @NonNull
        Class<E> type;

        /**
         * The value
         */
        private
        @Nullable
        E value;

        /**
         * Instantiates a new typed value.
         *
         * @param type  the type
         * @param value the value
         */
        public TypedValue(@NonNull Class<E> type, @Nullable E value) {
            this.type = type;
            this.value = value;
        }

        /**
         * Instantiate a new <code>null</code>-valued instance.
         *
         * @param <E>  the element type
         * @param type the type
         * @return the typed value containing <code>null</code> as value
         */
        public static <E> TypedValue<E> nullValue(Class<E> type) {
            return new TypedValue<E>(type, null);
        }

        /**
         * Gets the value, <code>null</code> if that is set.
         *
         * @return the value
         */
        public
        @Nullable
        E getValue() {
            return value;
        }

        /**
         * Gets the type of this value.
         *
         * @return the corresponding class object
         */
        public Class<E> getType() {
            return type;
        }

        /**
         * Checks if this object is of a type.
         * <p>
         * Caution: It is checked whether the types are <em>exactly</em> the
         * same. Subtype relations are not checked here.
         *
         * @param otherType the other type to check against
         * @return true, if is this's type and otherType are the same
         */
        public boolean isType(Class<?> otherType) {
            return getType() == otherType;
        }

        /**
         * Cast this typed value into one which has a known type parameter.
         * <p>
         * Due to the class' design, this method is type safe. Use it like
         * <p>
         * <pre>
         * TypeValue<?> tv;
         * // ... obtain from somewhere w/o knowing its type parameter
         * if (tv.isType(String.class)) {
         *     TypeValue<String> sv = tv.cast(String.class);
         *     String string = sv.getValue();
         * }
         * </pre>
         *
         * @param <F>       the type to cast to
         * @param otherType the class type into which it is to be cast
         * @return <code>this</code> but potentially with a different static
         * type
         */
        @SuppressWarnings("unchecked")
        public <F> TypedValue<F> cast(Class<F> otherType) {
            if (otherType == type) {
                return (TypedValue<F>) this;
            } else {
                throw new ClassCastException();
            }
        }
    }
}
