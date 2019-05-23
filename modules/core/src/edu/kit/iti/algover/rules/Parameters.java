/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import nonnull.NonNull;
import nonnull.Nullable;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
    private final Map<String, Object> valueMap;

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
     * Gets a value from the mapping.
     *
     * @param key
     *            the key to look up
     * @return the value stored for that variable, <code>null</code> if no such
     *         value
     */
    public @Nullable Object getValue(@NonNull String key) {
        return valueMap.get(key);
    }

    /**
     * Checks if a value is present in the mapping.
     *
     * @param param
     *            the key to look up
     */
    public boolean hasValue(@NonNull ParameterDescription<?> param) {
        return valueMap.containsKey(param.getName());
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
        Object value = valueMap.get(param.getName());
        if(value != null) {
            assert param.acceptsValue(value) :
                "This should have been checked way earlier! (see AbstractProofRule#checkParameters)";
            return param.castValue(value);
        }
        return null;
    }

    /**
     * Put a value into the mapping for a variable.
     *
     * @param key   the variable name
     * @param value the value to store.
     */
    public void putValue(@NonNull String key, @NonNull Object value) {
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
    public Set<Entry<String, Object>> entrySet() {
        return valueMap.entrySet();
    }

}
