/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.math.BigInteger;

import edu.kit.iti.algover.term.Term;

/**
 * This is an explicit enumeration type. Since type parameters are used, it is
 * not implemented as an {@link Enum} but as a class with static fields.
 *
 * <p> When a new script type is introduced, this class should get a new
 * constant.
 *
 * <p> The only real drawback against {@link Enum}s is that this class does not
 * support switch-case-statements.
 *
 * @param <T> the Java type which is associated with the script type
 */
public class ParameterType<T> {

    /**
     * The type to capture terms in parameters in scripts
     */
    public static final ParameterType<TermParameter> TERM =
            new ParameterType<>("Term", TermParameter.class);

    /**
     * The type to capture integers in parameters in scripts
     */
    public static final ParameterType<BigInteger> INTEGER =
            new ParameterType<>("Integer", BigInteger.class);

    /**
     * The type to capture booleans in parameters in scripts
     */
    public static final ParameterType<Boolean> BOOLEAN =
            new ParameterType<>("Boolean", Boolean.class);

    /**
     * The type to capture strings in parameters in scripts
     */
    public static final ParameterType<String> STRING =
            new ParameterType<>("String", String.class);

    /**
     * The readable name of the parameter type.
     */
    private final String name;

    /**
     * The Java classtype associated with the parameter.
     */
    private final Class<T> type;

    /**
     * Create a new parameter type.
     *
     * @param name name of the type to create
     * @param clzz the associated classtype.
     */
    private ParameterType(String name, Class<T> clzz) {
        this.name = name;
        this.type = clzz;
    }

    public String getName() {
        return name;
    }

    public Class<T> getType() {
        return type;
    }

    @Override
    public String toString() {
        return getName();
    }
}
