/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import nonnull.NonNull;

import java.util.Optional;

/**
 * Objects of this class contain descriptions of formal parameters to {@link
 * ProofRule}s.
 *
 * Usually parameters are used as static constant fields defined at load-time.
 *
 * They provide type-safe access to elements in a {@link Parameters} object if
 * their values have been checked beforehand using {@link
 * AbstractProofRule#checkParameters(Parameters)}.
 *
 * @param <T> The type of the values used in the parameter. Taken from the
 *            {@link ParameterType} provided as constructor argument.
 *
 * @author Mattias Ulbrich
 * @see ParameterType
 * @see Parameters
 */
public class ParameterDescription<T> {

    /**
     * The name of the parameter, i.e., the key under which it must be
     * specified.
     */
    private final String name;

    /**
     * The type of the parameter. Must be one of the constants defined in the
     * class.
     */
    private final ParameterType<T> type;

    /**
     * Is this a required (true) or optional (false) paramter.
     */
    private final boolean required;

    /**
     * This is the value this parameter will take if its not explicitly given.
     */
    private final Optional<T> defaultValue;

    /**
     * Instantiate a new immutable parameter description.
     *
     * @param name key for the parameter
     * @param type type of the parameter
     * @param required is the parameter required or optional?
     */
    public ParameterDescription(@NonNull String name, @NonNull ParameterType<T> type, boolean required) {
        this.name = name;
        this.type = type;
        this.required = required;
        this.defaultValue = Optional.empty();
    }
    /**
     * Instantiate a new immutable parameter description.
     *
     * @param name key for the parameter
     * @param type type of the parameter
     * @param required is the parameter required or optional?
     */
    public ParameterDescription(@NonNull String name, @NonNull ParameterType<T> type, boolean required, T defaultValue) {
        this.name = name;
        this.type = type;
        this.required = required;
        this.defaultValue = Optional.of(defaultValue);
    }

    /**
     * Check if the given value is compatible with the class type.
     *
     * @param value the object to check
     * @return true iff the value is an instance of the class
     * in the {@link ParameterType}.
     */
    public boolean acceptsValue(Object value) {
        return type.getType().isInstance(value);
    }

    /**
     * Cast the value into the type of parameter.
     *
     * @param value the object to cast
     * @return the same reference as value, but with a different type.
     * @throws ClassCastException if the object is not null and is not
     *                            assignable to the type.
     */
    public T castValue(Object value) {
        return type.getType().cast(value);
    }

    public String getName() {
        return name;
    }

    public boolean isRequired() {
        return required;
    }

    public ParameterType<T> getType() {
        return type;
    }

    public Optional<T> getDefaultValue() {
        return defaultValue;
    }
}
