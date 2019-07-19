/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import nonnull.NonNull;
import nonnull.Nullable;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiConsumer;

/**
 * The Class Parameters is used to provide concrete arguments to {@link
 * ProofRuleApplication}s.
 *
 * <p> It is essentially a map from names (Strings) to values ({@link Object}).
 *
 * <p> An instance can be set immutable ({@link #setImmutable()}). Thus its
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
     * The storage mapping variable names to values.
     */
    private final Map<ParameterDescription<?>, Object> valueMap;

    /**
     * The mutability flag. Can never be set back to true once set to false.
     */
    private boolean mutable = true;

    /**
     * Instantiates a new empty parameter mapping.
     */
    public Parameters() {
        this.valueMap = new LinkedHashMap<>();
    }

    /**
     * Instantiates a new parameter mapping from another mapping.
     *
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
     * Checks if a value is present in the mapping.
     *
     * @param param
     *            the key to look up
     */
    public boolean hasValue(@NonNull ParameterDescription<?> param) {
        return valueMap.containsKey(param);
    }

    /**
     * Gets a value from the mapping.
     *
     * The key to look up is taken from the name in the parameter description
     * via {@link ParameterDescription#getName()}.
     *
     * @param param the parameter description to look up.
     * @return the value stored for that variable, <code>null</code> if no such
     * value
     * @throws ClassCastException if the value is not assign-compatible with the
     *                            type in the parameter description.
     */
    public @Nullable <T> T getValue(@NonNull ParameterDescription<T> param) {
        Object value = valueMap.get(param);
        if(value != null) {
            assert param.acceptsValue(value) :
                "This should have been checked way earlier! (see AbstractProofRule#checkParameters)";
            return param.castValue(value);
        }
        if (param.getDefaultValue().isPresent()) {
            return param.getDefaultValue().get();
        }
        return null;
    }

    /**
     * Gets a value from the mapping or a default value if the key is absent.
     *
     * The key to look up is taken from the name in the parameter description
     * via {@link ParameterDescription#getName()}.
     *
     * If that key is not in this map, the second parameter is returned
     *
     * @param param the parameter description to look up.
     * @param defaultValue the value returned if param is not set
     * @return the value stored for that variable, <code>defaultValue</code>
     * if no such value
     * @throws ClassCastException if the value is not assign-compatible with the
     *                            type in the parameter description.
     */
    @Deprecated //added default values
    public <T> T getValueOrDefault(ParameterDescription<T> param, T defaultValue) {
        if (hasValue(param)) {
            return getValue(param);
        } else {
            return defaultValue;
        }
    }

    /**
     * Put a value into the mapping for a variable.
     *
     * @param key   the variable name
     * @param value the value to store.
     * @param <T> the value type of the parameter.
     */
    public <T> void putValue(@NonNull ParameterDescription<T> key, @NonNull T value) {
        if (!isMutable()) {
            throw new IllegalStateException("These parameters are immutable");
        }
        // That is an extra sanity check. The type system should not allow that
        // to fail.
        assert key.acceptsValue(value);
        valueMap.put(key, value);
    }

    /**
     * Put a value into the mapping for a variable.
     *
     * @param key   the variable name
     * @param value the value to store.
     * @param <T> the value type of the parameter.
     */
    public <T> void checkAndPutValue(@NonNull ParameterDescription<T> key, @NonNull Object value) {
        if (!isMutable()) {
            throw new IllegalStateException("These parameters are immutable");
        }
        if (!key.acceptsValue(value)) {
            throw new IllegalArgumentException();
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
    public Set<Entry<ParameterDescription<?>, Object>> entrySet() {
        return valueMap.entrySet();
    }

    /**
     * Checks if this object is empty, i.e. if there are any parameters set
     * in it or none at all.
     *
     * @return true iff there are no parameters set
     */
    public boolean isEmpty() {
        return valueMap.isEmpty();
    }

    /**
     * Checks if this object contains at least the parameters (not necessarily)
     * the values also set in the argument.
     *
     * @param parameters to compare with
     * @return true iff my keys are a superset of the argument's keys
     */
    public boolean containsKeys(@NonNull  Parameters parameters) {
        return valueMap.keySet().containsAll(parameters.valueMap.keySet());
    }
}
