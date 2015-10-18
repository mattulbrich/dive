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
    }

    public ApplTerm(FunctionSymbol function, Term... arguments) {
        this(function, Arrays.asList(arguments));
    }

    public ApplTerm(FunctionSymbol constant) {
        this(constant, Collections.emptyList());
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
