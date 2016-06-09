/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;


import edu.kit.iti.algover.util.Util;

public class ApplTerm extends Term {

    private final FunctionSymbol function;

    public ApplTerm(FunctionSymbol function, List<Term> arguments) {
        super(function.getResultSort(), Util.toArray(arguments, Term.class));
        this.function = function;
//        check();
    }

    public ApplTerm(FunctionSymbol function, Term... arguments) {
        this(function, Arrays.asList(arguments));
    }

    public ApplTerm(FunctionSymbol constant) {
        this(constant, Collections.emptyList());
    }

    private void check() {
        if(function.getArity() != getSubterms().size()) {
            throw new RuntimeException("Illegal number of arguments");
        }
        for (int i = 0; i < function.getArity(); i++) {
            Sort expected = function.getArgumentSorts().get(i);
            Sort is = getSubterms().get(i).getSort();
            if(!is.equals(expected)) {
                throw new RuntimeException("Unexpected argument sort");
            }
        }
    }

    @Override
    public String toString() {
        if(function.getArity() == 0) {
            return function.getName();
        } else {
            return function.getName() + "(" + Util.commatize(getSubterms()) + ")";
        }
    }

    @Override
    public <A, R> R accept(TermVisitor<A, R> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public FunctionSymbol getFunctionSymbol() {
        return function;
    }

}
