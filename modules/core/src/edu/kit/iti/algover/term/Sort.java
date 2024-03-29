/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Util;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;

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

@NonNull
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
     *
     * @deprecated Use {@link #BOOL} instead.
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
     * of an untyped {@link SchemaTerm}.
     *
     * (Would be an existential type)
     */
    public static final Sort UNTYPED_SORT = get("$UNTYPED");

    /**
     * The uninhabited bottom type of the type hierarchy.
     *
     * Used for empty sets and sequences ...
     */
    public static final Sort BOTTOM = get("$nothing");

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
        BUILTIN_SORT_NAMES.add("multiset");
        BUILTIN_SORT_NAMES.add("seq");
        BUILTIN_SORT_NAMES.add("array");
        BUILTIN_SORT_NAMES.add("array2");
        BUILTIN_SORT_NAMES.add("array3");
        BUILTIN_SORT_NAMES.add("field");
        BUILTIN_SORT_NAMES.add("heap");
        BUILTIN_SORT_NAMES.add("$nothing");
        BUILTIN_SORT_NAMES.add("$tuple");
    }

    /**
     * Instantiates a new sort w/ arguments.
     *
     * @param name
     *            the non-<code>null</code> name
     * @param arguments
     *            the deep-non-<code>null</code> arguments
     */
    private Sort(@NonNull String name, @DeepNonNull Sort... arguments) {
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
    public static Sort get(@NonNull String name) {
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
    public static @NonNull Sort get(@NonNull String name, @DeepNonNull Sort... arguments) {
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
    public static @NonNull Sort get(@NonNull String name, @DeepNonNull Collection<Sort> arguments) {
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
    public static @NonNull Sort getClassSort(@NonNull String name) {
        assert !BUILTIN_SORT_NAMES.contains(name);
        return get(name, NO_ARGUMENTS);
    }

    /**
     * Gets the name of this sort (w/o arguments).
     *
     * @return the non-<code>null</code> name of the sort
     */
    public @NonNull String getName() {
        return name;
    }

    @Override
    public @NonNull String toString() {
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
    private @Nullable Sort instantiate0(List<Sort> instantiationSorts) {
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
    public @NonNull Sort instantiate(@DeepNonNull List<Sort> instantiationSorts) {
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
    public @DeepNonNull List<Sort> getArguments() {
        return Util.readOnlyArrayList(arguments);
    }

    /**
     * Gets a type argument of this sort instance.
     *
     * @return the argument at position index.
     * @throws IndexOutOfBoundsException if the index does not refer to a valid
     *                                   argument index
     */
    public @NonNull Sort getArgument(int index) {
        return arguments[index];
    }

    /**
     * Checks if this sort belongs to a Dafny class.
     *
     * Checks if the name is a builtin name.
     *
     * @return <code>true</code>, iff this objects represents the sort for a
     *         Dafny class
     */
    public boolean isClassSort() {
        return !BUILTIN_SORT_NAMES.contains(getName());
    }

    /**
     * Checks if this sort is a reference sort.
     *
     * This is the case for object, classes and arrays.
     *
     * Equivalent to calling {@code isSubtypeOf(OBJECT)}.
     *
     * @return <code>true</code>, iff this objects represents a ref type.
     */
    public boolean isReferenceSort() {
        return isSubtypeOf(OBJECT);
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
    public boolean isSubtypeOf(@NonNull Sort other) {

        if (equals(other)) {
            return true;
        }

        if(equals(UNTYPED_SORT)) {
            return true;
        }

        if (equals(BOTTOM) && !other.equals(UNTYPED_SORT)) {
            return true;
        }

        if(isClassSort() || isArray()) {
            return other.equals(OBJECT);
        }

        if(equals(NULL)) {
            return other.isClassSort() || other.equals(OBJECT) || other.isArray();
        }

        if(name.equals(other.name)) {
            switch (name) {
            case "set":
            case "multiset":
            case "seq":
                return getArgument(0).isSubtypeOf(other.getArgument(0));
            case "$tuple":
                if (arguments.length != other.arguments.length) {
                    return false;
                }
                for (int i = 0; i < arguments.length; i++) {
                    if(!getArgument(i).isSubtypeOf(other.getArgument(i))) {
                        return false;
                    }
                }
                return true;
            // case "map": that would be contravariant in the first argument!
            }
        }

        return false;
    }

    public boolean isArray() {
        return getName().matches("array[23]?");
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + Arrays.hashCode(arguments);
        return result;
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        Sort sort = (Sort) o;

        if (!name.equals(sort.name)) {
            return false;
        }
        return Arrays.equals(arguments, sort.arguments);
    }

    /**
     * Compute the common super sort for the two arguments if it exists.
     * If it does not exist, an exception is raised.
     *
     * @param sort1 the first sort to compare
     * @param sort2 the second sort to compare
     * @return the most specific sort which is top sort to both arguments.
     * @throws TermBuildException if there is no common supersort
     */
    public static @NonNull Sort supremum(@NonNull Sort sort1, @NonNull Sort sort2) throws TermBuildException {
        if(sort1.isSubtypeOf(sort2)) {
            return sort2;
        }

        if(sort2.isSubtypeOf(sort1)) {
            return sort1;
        }

        if((sort1.isClassSort() || sort1.isArray()) &&
           (sort2.isClassSort() || sort2.isArray())) {
            return OBJECT;
        }

        if(sort1.name.equals(sort2.name)) {
            switch (sort1.name) {
            case "set":
            case "multiset":
            case "seq":
                Sort innersup = supremum(sort1.getArgument(0), sort2.getArgument(0));
                return get(sort1.name, innersup);
            // case "map": that would be contravariant in the first argument!
            }
        }

        throw new TermBuildException("No common supertype for " + sort1 + " and " + sort2);
    }

    /**
     * Parse a String into a Sort.
     *
     * @param sortString a string that could be produced by String{@link
     *                   #toString()}
     * @return a fresh Sort object.
     * @throws IllegalArgumentException if the string cannot be parsed to a
     *                                  sort
     */
    public static @NonNull Sort parseSort(@NonNull String sortString) {
        return parseSort(sortString, new AtomicInteger());
    }

    private static @NonNull Sort parseSort(@NonNull String sortString, @NonNull AtomicInteger pos) {
        StringBuilder sb = new StringBuilder();
        int len = sortString.length();
        while(pos.get() < len) {
            char c = sortString.charAt(pos.get());
            if ("<>,".indexOf(c) != -1) {
                break;
            }
            if("\t ".indexOf(c) == -1) {
                // overread spaces and tabs
                sb.append(c);
            }
            pos.incrementAndGet();
        }

        List<Sort> children = null;
        if(pos.get() < len) {
            char c = sortString.charAt(pos.get());
            if(c != '<') {
                return Sort.get(sb.toString());
            }
            pos.incrementAndGet();
            children = new ArrayList<>();
            children.add(parseSort(sortString, pos));
        }

        while(pos.get() < len) {
            char c = sortString.charAt(pos.get());
            pos.incrementAndGet();
            switch(c) {
            case ',':
                children.add(parseSort(sortString, pos));
                break;
            case '>':
                return Sort.get(sb.toString(), children);
            default:
                throw new IllegalArgumentException();
            }
        }

        return Sort.get(sb.toString());
    }
}