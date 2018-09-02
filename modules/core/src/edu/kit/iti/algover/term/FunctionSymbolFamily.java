/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

/**
 * A function symbol family is a template for function symbols instantiated with
 * concrete sorts.
 *
 * The family can be something like {@code single<?1> : ?1 -> set<?1>} that
 * takes an element of some type {@code ?1} and wraps it into a set of type
 * {@code set<?1>}.
 *
 * <b>Warning:</b> Do not use the methods {@link #instantiate(Sort...)} or {@link #instantiate(List)}
 * but better go over the {@link edu.kit.iti.algover.data.SymbolTable} via
 * {@link edu.kit.iti.algover.data.SymbolTable#getFunctionSymbol(FunctionSymbolFamily, Sort...)}.
 *
 * @author mulbrich
 */
public class FunctionSymbolFamily {

    /**
     * A constant for the first sort variable used in a symbol family.
     */
    public static final Sort VAR1 = Sort.get("?1");

    /**
     * A constant for the 2nd sort variable used in a symbol family.
     */
    public static final Sort VAR2 = Sort.get("?2");

    /**
     * A constant for the 3rd sort variable used in a symbol family.
     */
    public static final Sort VAR3 = Sort.get("?3");

    /**
     * how many type variables are there for this symbol family.
     */
    private int numberOfTypeVars;

    /**
     * the template which is used to instantiate the concrete symbols from.
     */
    private @NonNull FunctionSymbol prototype;

    /**
     * Create a fresh symbol family from a prototype
     *
     * @param prototype        the function defintion used for instantiation
     * @param numberOfTypeVars number of type variables occurring in this
     *                         defnition
     */
    public FunctionSymbolFamily(@NonNull FunctionSymbol prototype,
                                int numberOfTypeVars) {
        this.prototype = prototype;
        this.numberOfTypeVars = numberOfTypeVars;
    }

    /**
     * Instantiate this family with concrete sorts.
     *
     * @param instantiationSorts the sort to instantiate the template with.
     * @return a freshly created function symbol.
     * @throws IllegalArgumentException if the number of instantiated sorts is
     *                                  not right
     */
    public @NonNull FunctionSymbol instantiate(Sort... instantiationSorts) {
        return instantiate(Arrays.asList(instantiationSorts));
    }

    /**
     * Instantiate this family with concrete sorts.
     *
     * @param instantiationSorts the sort to instantiate the template with.
     * @return a freshly created function symbol.
     * @throws IllegalArgumentException if the number of instantiated sorts is
     *                                  not right
     */
    public FunctionSymbol instantiate(List<Sort> instantiationSorts) {

        if(instantiationSorts.size() != numberOfTypeVars) {
            throw new IllegalArgumentException(instantiationSorts + " vs. " + numberOfTypeVars);
        }

        String name = prototype.getName() +
                toString(instantiationSorts);

        Sort resSort = prototype.getResultSort().instantiate(instantiationSorts);

        List<Sort> argSorts = Util.map(prototype.getArgumentSorts(),
                x -> x.instantiate(instantiationSorts));

        return new InstantiatedFunctionSymbol(name, resSort, argSorts,
                instantiationSorts);
    }

    /**
     * Turn a list of sorts into a suffix for a function name that would be
     * appended to identify the instance.
     *
     * <p>For example make {@code <X,Y<Z>>} from {@code [X, Y<Z>]}.</p>
     *
     * @param instantiationSorts the concrete types to create the string from.
     * @return a string representation of the suffix induced by the
     * instantiation sorts
     */
    public static String toString(List<Sort> instantiationSorts) {
        if (instantiationSorts.isEmpty()) {
            return "";
        } else {
            return "<" + Util.join(instantiationSorts, ",") + ">";
        }
    }

    /**
     * Decode a parameterised function symbols into its parameters.
     *
     * @param parametrisedFunction
     *            the string of a function with parameters {@code ...<...>}
     * @return an immutable list of sorts
     */
    public static @NonNull List<Sort> parseSortParameters(@NonNull String parametrisedFunction) {
        List<Sort> sorts = parseSort0(parametrisedFunction, new AtomicInteger()).getArguments();
        return sorts;
    }

    private static Sort parseSort0(String string, AtomicInteger pos) {
        StringBuilder name = new StringBuilder();
        while(pos.get() < string.length() &&
                "<>,".indexOf(string.charAt(pos.get())) == -1) {
            name.append(string.charAt(pos.get()));
            pos.incrementAndGet();
        }

        if(pos.get() < string.length() &&
                string.charAt(pos.get()) == '<') {
            List<Sort> args = new LinkedList<>();
            do {
                pos.incrementAndGet();
                args.add(parseSort0(string, pos));
            } while(pos.get() < string.length() &&
                    string.charAt(pos.get()) == ',');

            assert pos.get() == string.length() || string.charAt(pos.get()) == '>';
            pos.incrementAndGet();

            return Sort.get(name.toString(), args);
        } else {
            return Sort.get(name.toString());
        }
    }

    /**
     * A function symbol which is induced by instantiation of a symbol family.
     */
    public class InstantiatedFunctionSymbol extends FunctionSymbol {

        private final List<Sort> instantiations;

        public InstantiatedFunctionSymbol(String name,
                Sort resultSort,
                List<Sort> argSorts,
                List<Sort> instantiationSorts) {
            super(name, resultSort, argSorts);
            this.instantiations = instantiationSorts;
        }

        public FunctionSymbolFamily getFamily() {
            return FunctionSymbolFamily.this;
        }

        public List<Sort> getInstantiations() {
            return Collections.unmodifiableList(instantiations);
        }

    }

    /**
     * Get the basename of the symbol, that is the part before the {@code <...>}.
     * @return the basename
     */
    public @NonNull String getBaseName() {
        return prototype.getName();
    }

    @Override
    public String toString() {
        return "FunctionSymbolFamily [" + prototype + ", #vars=" + numberOfTypeVars + "]";
    }

}
