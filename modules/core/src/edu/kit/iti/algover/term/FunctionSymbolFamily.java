/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.util.Util;

public class FunctionSymbolFamily {

    public static final Sort VAR1 = new Sort("?1");
    public static final Sort VAR2 = new Sort("?1");
    public static final Sort VAR3 = new Sort("?1");

    private int numberOfTypeVars;
    private FunctionSymbol prototype;

    public FunctionSymbolFamily(FunctionSymbol prototype,
            int numberOfTypeVars) {
        this.prototype = prototype;
        this.numberOfTypeVars = numberOfTypeVars;
    }

    public FunctionSymbol instantiate(List<Sort> instantiationSorts) {

        if(instantiationSorts.size() != numberOfTypeVars) {
            throw new IllegalArgumentException();
        }

        String name = prototype.getName() +
                (instantiationSorts.toString().replace(" ", ""));

        Sort resSort = prototype.getResultSort().instantiate(instantiationSorts);

        List<Sort> argSorts = Util.map(prototype.getArgumentSorts(),
                x -> x.instantiate(instantiationSorts));

        return new InstantiatedFunctionSymbol(name, resSort, argSorts,
                instantiationSorts);
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
