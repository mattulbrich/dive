package edu.kit.iti.algover.term;

import java.util.List;

import edu.kit.iti.algover.util.Util;

public class ApplTerm extends Term {

    private FunctionSymbol function;

    public ApplTerm(FunctionSymbol function, List<Term> arguments) {
        super(function.getResultSort(), Util.toArray(arguments, Term.class));
        this.function = function;
    }

    @Override
    public String toString() {
        if(function.getArity() == 0) {
            return function.getName();
        } else {
            return function.getName() + "(" + Util.commatize(getSubterms()) + ")";
        }
    }

}
