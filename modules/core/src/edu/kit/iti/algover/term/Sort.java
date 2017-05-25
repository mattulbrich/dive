/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import edu.kit.iti.algover.util.Util;

/**
 * The Class Sort.
 */
public class Sort {

    // Checkstyle: OFF DeclarationOrderCheck

    /**
     * This array is used if a type as no further structure.
     *
     * (Must be first field in class)
     */
    private static final Sort[] NO_ARGUMENTS = new Sort[0];

    /**
     * The Constant FORMULA captures the boolean type. It may be that this will
     * be renamed to boolean eventually.
     */
    public static final Sort FORMULA = new Sort("formula");

    /**
     * The Constant INT captures the builtin integer type.
     */
    public static final Sort INT = new Sort("int");

    /**
     * The Constant INT captures the builtin boolean type.
     */
    public static final Sort BOOL = new Sort("bool");

    /**
     * The Constant INT_SET is the typo of sets of integers.
     * Since this type is a member of the initial-language support,
     * it is added as a constant here.
     */
    public static final Sort INT_SET = new Sort("set", INT);

    /**
     * The Constant HEAP for the heap sort.
     */
    public static final Sort HEAP = new Sort("heap");

    /**
     * The Constant REF for the reference type.
     */
    public static final Sort REF = new Sort("ref");

    /**
     * The Constant FIELD for the (polymorphic) field datatype.
     */
    public static final Sort FIELD = new Sort("field");

    /**
     * The name of the type (w/o arguments).
     */
    private final String name;

    /**
     * The arguments, must not be <code>null</code>.
     */
    private final Sort[] arguments;

    /**
     * Instantiates a new sort w/o arguments.
     *
     * @param name
     *            the non-<code>null</code> name
     */
    public Sort(String name) {
        this(name, NO_ARGUMENTS);
    }

    /**
     * Instantiates a new sort w/ arguments.
     *
     * @param name
     *            the non-<code>null</code> name
     * @param arguments
     *            the deep-non-<code>null</code> arguments
     */
    public Sort(String name, Sort... arguments) {
        this.name = Objects.requireNonNull(name);
        this.arguments = Util.requireDeepNonNull(arguments);
    }

    @Override
    public int hashCode() {
        return name.hashCode() + 31 * Arrays.hashCode(arguments);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Sort) {
            Sort sort = (Sort) obj;
            return name.equals(sort.name)
                && Arrays.equals(arguments, sort.arguments);
        }
        return false;
    }

    /**
     * Gets the name of this sort (w/o arguments).
     *
     * @return the non-<code>null</code> name of the sort
     */
    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        if (arguments.length > 0) {
            return getName() + "<" + Util.join(arguments, ",") + ">";
        } else {
            return getName();
        }
    }

    /*
     * Internal instantiation.
     *
     * It lazily creates new arrays and returns null if nothing has changed.
     */
    private Sort instantiate0(List<Sort> instantiationSorts) {
        if (getName().startsWith("?")) {
            int index = Integer.parseInt(name.substring(1));
            return instantiationSorts.get(index - 1);
        }

        Sort[] newArgs = null;
        for (int i = 0; i < arguments.length; i++) {
            Sort newArg = arguments[i].instantiate0(instantiationSorts);
            if (newArg != null) {
                if (newArgs == null) {
                    newArgs = arguments.clone();
                }
                newArgs[i] = newArg;
            }
        }

        if (newArgs == null) {
            return null;
        }

        return new Sort(name, newArgs);
    }

    /**
     * Instantiate type variables in a type.
     *
     * This means that for a positive number i every occurrence of "?i" is
     * replaced by the i-th element of the instantiation sorts.
     *
     * @param instantiationSorts
     *            the non-<code>null</code> instantiation sorts to be used
     * @throws IndexOutOfBoundsException
     *             if there is a type variable "?i" for an index outside the
     *             range of the instantiation sorts.
     * @return the instantiated sort, not <code>null</code>
     */
    public Sort instantiate(List<Sort> instantiationSorts) {
        Sort result = instantiate0(instantiationSorts);
        if (result != null) {
            return result;
        } else {
            return this;
        }
    }

    /**
     * Gets the type arguments of this sort instance.
     *
     * @return an unmodifiable list of types.
     */
    public List<Sort> getArguments() {
        return Util.readOnlyArrayList(arguments);
    }

}
