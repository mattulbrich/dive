/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import edu.kit.iti.algover.util.Util;

/**
 * The Class Sort models a sort-type in the logic.

 * To allow for future memory footprint optimisations, the constructor is
 * hidden. Thus, a canoncalising cache class could be added.
 *
 * <h3>Subtypes</h3>
 *
 * The subtype relation is modelled using the {@link #isSubtypeOf(Sort)}
 * method.
 *
 * The type hierarchy is very simple such that it is hard coded into this class:
 * Type <code>A</code> is subtype of type <code>B</code> iff
 * <ol>
 * <li><code>A</code> is type <code>object</code> and B is either type
 * <code>null</code> or a class type.
 * <li><code>A</code> is a class type and <code>B</code> is the null type.
 * </ol>
 *
 * All sorts which are not in the set of builtin sorts are considered class
 * types.
 *
 * @author mulbrich
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
     * The Constant INT captures the builtin integer type.
     */
    public static final Sort INT = get("int");

    /**
     * The Constant BOOL captures the builtin boolean type.
     */
    public static final Sort BOOL = get("bool");

    /**
     * The Constant FORMULA captures the boolean type. It may be that this will
     * be renamed to boolean eventually.
     */
    @Deprecated
    public static final Sort FORMULA = BOOL;

    /**
     * The Constant INT_SET is the typo of sets of integers.
     * Since this type is a member of the initial-language support,
     * it is added as a constant here.
     */
    public static final Sort INT_SET = get("set", INT);

    /**
     * The Constant HEAP for the heap sort.
     */
    public static final Sort HEAP = get("heap");

    /**
     * The Constant OBJECT for the object type.
     */
    public static final Sort OBJECT = get("object");

    /**
     * The Constant NULL for the null type.
     */
    public static final Sort NULL = get("null");

    /**
     * The Constant UNTYPED_SORT for the totally arbitrary type
     * of an untyped {@link SchemaVarTerm}.
     *
     * (Would be an existential type)
     */
    public static final Sort UNTYPED_SORT = get("$UNTYPED");

    /**
     * The name of the type (w/o arguments).
     */
    private final String name;

    /**
     * The arguments, must not be <code>null</code>.
     */
    private final Sort[] arguments;

    private static final Set<String> BUILTIN_SORT_NAMES;

    static {
        BUILTIN_SORT_NAMES = new HashSet<>();
        BUILTIN_SORT_NAMES.add(INT.getName());
        BUILTIN_SORT_NAMES.add(BOOL.getName());
        BUILTIN_SORT_NAMES.add(HEAP.getName());
        BUILTIN_SORT_NAMES.add(OBJECT.getName());
        BUILTIN_SORT_NAMES.add(NULL.getName());
        BUILTIN_SORT_NAMES.add("set");
        BUILTIN_SORT_NAMES.add("seq");
        BUILTIN_SORT_NAMES.add("array");
        BUILTIN_SORT_NAMES.add("array2");
        BUILTIN_SORT_NAMES.add("array3");
        BUILTIN_SORT_NAMES.add("field");
        BUILTIN_SORT_NAMES.add("heap");
    }

    /**
     * Instantiates a new sort w/ arguments.
     *
     * @param name
     *            the non-<code>null</code> name
     * @param arguments
     *            the deep-non-<code>null</code> arguments
     */
    private Sort(String name, Sort... arguments) {
        this.name = Objects.requireNonNull(name);
        this.arguments = Util.requireDeepNonNull(arguments);

        assert !name.contains("<") : "Sort name with '<': " + name;
    }

    /**
     * Gets a sort object by name.
     *
     * No arguments, not a class type.
     *
     * @param name
     *            the name of the sort to look up.
     * @return the sort can be a fresh object or taken from a cache.
     */
    public static Sort get(String name) {
        // could use Cache object if needed
        return new Sort(name, NO_ARGUMENTS);
    }

    /**
     * Gets a sort object by name and arguments.
     *
     * @param name
     *            the name of the sort to look up.
     * @param arguments
     *            non-<code>null</code> sorts that parametrise the object
     *
     * @return the sort can be a fresh object or taken from a cache.
     */
    public static Sort get(String name, Sort... arguments) {
        // could use Cache object if needed
        return new Sort(name, arguments);
    }

    /**
     * Gets a sort object by name and arguments.
     *
     * @param name
     *            the name of the sort to look up.
     * @param arguments
     *            non-<code>null</code> sorts that parametrise the object
     *
     * @return the sort can be a fresh object or taken from a cache.
     */
    public static Sort get(String name, Collection<Sort> arguments) {
        return Sort.get(name, (Sort[]) arguments.toArray(new Sort[arguments.size()]));
    }

    /**
     * Gets a sort object by name.
     *
     * The resulting object is a class sort ({@link #isClassSort()}) and has no
     * arguments.
     *
     * @param name
     *            the name of the sort to look up.
     * @return the sort can be a fresh object or taken from a cache.
     */
    public static Sort getClassSort(String name) {
        assert !BUILTIN_SORT_NAMES.contains(name);
        return new Sort(name, NO_ARGUMENTS);
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
                && isClassSort() == sort.isClassSort()
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

        return get(name, newArgs);
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

    /**
     * Checks if this sort belongs to a Dafny class.
     *
     * Checks if the name is a builtin name
     *
     * @return <code>true</code>, iff this objects reprsents the sort for a
     *         Dafny class
     */
    public boolean isClassSort() {
        return !BUILTIN_SORT_NAMES.contains(getName());
    }

    /**
     * Checks if this sort is a subtype/subsort of its argument.
     *
     * @param other
     *            the non-<code>null</code> other sort
     *
     * @return true, if this object represents a sort which is subtype of the
     *         argument.
     */
    public boolean isSubtypeOf(Sort other) {
        if(equals(UNTYPED_SORT)) {
            return true;
        }

        if(isClassSort() || isArray()) {
            return equals(other) || other.equals(OBJECT);
        }

        if(equals(NULL)) {
            return equals(other) || other.isClassSort() || other.equals(OBJECT) || other.isArray();
        }

        return equals(other);
    }

    private boolean isArray() {
        return getName().matches("array[23]?");
    }

}