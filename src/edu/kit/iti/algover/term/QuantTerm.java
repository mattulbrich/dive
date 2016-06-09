/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import edu.kit.iti.algover.term.builder.TermBuildException;

public class QuantTerm extends Term {

    public enum Quantifier {
        FORALL, EXISTS
    };

    private final VariableTerm boundVar;
    private final Quantifier quantifier;

    public QuantTerm(Quantifier quantifier, VariableTerm boundVar, Term term) throws TermBuildException {
        super(Sort.FORMULA, new Term[] { term });
        this.boundVar = boundVar;
        this.quantifier = quantifier;

        if(!term.getSort().equals(Sort.FORMULA)) {
            throw new TermBuildException("Cannot quantify over " + term + "; it is not a formula.");
        }
    }

    @Override
    public String toString() {
        return "(" + quantifier + " " + boundVar + ":" + boundVar.getSort()
                + " :: " + getTerm(0) + ")";
    }

    @Override
    public <A, R> R accept(TermVisitor<A, R> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public VariableTerm getBoundVar() {
        return boundVar;
    }

    public Quantifier getQuantifier() {
        return quantifier;
    }

}
