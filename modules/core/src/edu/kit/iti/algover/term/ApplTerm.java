/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Util;

public class ApplTerm extends Term {

    private final FunctionSymbol function;

    public ApplTerm(FunctionSymbol function, List<? extends Term> arguments) throws TermBuildException {
        super(function.getResultSort(),
                Util.toArray(arguments, Term.class));
        this.function = function;
        check();
    }

    public ApplTerm(FunctionSymbol function, Term... arguments) throws TermBuildException {
        this(function, Arrays.asList(arguments));
    }

    public ApplTerm(FunctionSymbol constant) throws TermBuildException {
        this(constant, Collections.emptyList());
    }

    private void check() throws TermBuildException {
        if (function.getArity() != getSubterms().size()) {
            throw new TermBuildException("Illegal number of arguments to " + function +
                    ", received " + getSubterms().size());
        }

        for (int i = 0; i < function.getArity(); i++) {
            Sort expected = function.getArgumentSorts().get(i);
            Sort is = getSubterms().get(i).getSort();
            if (!is.isSubtypeOf(expected)) {
                throw new TermBuildException("Unexpected argument sort for argument " +
                        (i + 1) + " to " + function
                        + ", expected " + expected + " but received " + is);
            }
        }
    }

    @Override
    public String toString() {
        if (function.getArity() == 0) {
            return function.getName();
        } else {
            return function.getName() + "(" + Util.commatize(getSubterms()) + ")";
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (!super.equals(obj)) {
            return false;
        }

        // it is sure that obj is of type ApplFunction
        return ((ApplTerm) obj).function.equals(function);
    }

    @Override
    public <A, R, E extends Exception>
            R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

    public FunctionSymbol getFunctionSymbol() {
        return function;
    }

}
