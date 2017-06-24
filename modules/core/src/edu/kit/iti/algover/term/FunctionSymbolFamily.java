/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.util.Util;

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
    private String toString(List<Sort> instantiationSorts) {
        if (instantiationSorts.isEmpty()) {
            return "";
        } else {
            return "<" + Util.join(instantiationSorts, ",") + ">";
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

}
