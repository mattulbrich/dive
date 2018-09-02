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

public class FunctionSymbolFamily {

    public static final Sort VAR1 = Sort.get("?1");
    public static final Sort VAR2 = Sort.get("?2");
    public static final Sort VAR3 = Sort.get("?3");

    private int numberOfTypeVars;
    private FunctionSymbol prototype;

    public FunctionSymbolFamily(FunctionSymbol prototype,
            int numberOfTypeVars) {
        this.prototype = prototype;
        this.numberOfTypeVars = numberOfTypeVars;
    }

    public FunctionSymbol instantiate(Sort ... instantiationSorts) {
        return instantiate(Arrays.asList(instantiationSorts));
    }

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

    /*
     * make <X,Y<Z>> from [X, Y<Z>]
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

    public String getBaseName() {
        return prototype.getName();
    }

    @Override
    public String toString() {
        return "FunctionSymbolFamily [" + prototype + ", #vars=" + numberOfTypeVars + "]";
    }

}
