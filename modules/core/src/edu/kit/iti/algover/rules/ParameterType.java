/*
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.math.BigInteger;

import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.Util;

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
 *
 * @author Mattias Ulbrich
 */
public abstract class ParameterType<T> {

    /**
     * The type to capture terms in parameters in scripts
     */
    public static final ParameterType<TermParameter> TERM =
            new ParameterType<>("Term", TermParameter.class) {
                @Override
                public String prettyPrint(PrettyPrint prettyPrint, TermParameter value) {
                    return prettyPrintTerm(prettyPrint, value);
                }
            };

    /**
     * The type to capture integers in parameters in scripts
     */
    public static final ParameterType<BigInteger> INTEGER =
            new ParameterType<>("Integer", BigInteger.class) {
                @Override
                public String prettyPrint(PrettyPrint prettyPrint, BigInteger value) {
                    return value.toString();
                }
            };

    /**
     * The type to capture booleans in parameters in scripts
     */
    public static final ParameterType<Boolean> BOOLEAN =
            new ParameterType<>("Boolean", Boolean.class) {
                @Override
                public String prettyPrint(PrettyPrint prettyPrint, Boolean value) {
                    return value.toString();
                }
            };

    /**
     * The type to capture strings in parameters in scripts
     */
    public static final ParameterType<String> STRING =
            new ParameterType<>("String", String.class) {
                @Override
                public String prettyPrint(PrettyPrint prettyPrint, String value) {
                    return Util.quote(Util.escapeString(value));
                }
            };

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

    /**
     * Print this the parameter value provided in a nice form, possibly using the provided term
     * prettyprinter.
     *
     * Delimiters are added to the string (e.g. "..." for Strings).
     *
     * @param prettyPrint the pretty-printer for terms and sequents
     * @param value the value to print
     * @return a String representing the value
     */
    public abstract String prettyPrint(PrettyPrint prettyPrint, T value);

    // used from TermParameter#prettyPrint.
    private static String prettyPrintTerm(PrettyPrint prettyPrint, TermParameter parameter) {
        String pp;
        // TODO This case distinction is ugly.
        // TODO Make this into term parameter and optimise
        if (parameter.getOriginalTerm() != null) {
            pp = prettyPrint.print(parameter.getOriginalTerm()).toString();
        } else if (parameter.getOriginalSchematicTerm() != null) {
            pp = prettyPrint.print(parameter.getOriginalSchematicTerm()).toString();
        } else {
            try {
                pp = prettyPrint.print(parameter.getSchematicSequent()).toString();
            } catch (RuleException e) {
                // FIXME
                e.printStackTrace();
                pp = "UNKNOWN";
            }
        }
        return "'" + pp + "'";
    }
}
