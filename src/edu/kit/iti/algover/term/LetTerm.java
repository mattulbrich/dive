/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.util.Pair;

public class LetTerm extends Term {

    private final List<Pair<VariableTerm, Term>> substitutions;

    public LetTerm(VariableTerm var, Term expression, Term in) {
        this(Collections.singletonList(new Pair<>(var, expression)), in);
    }

    public LetTerm(List<Pair<VariableTerm, Term>> substs, Term in) {
        super(in.getSort(), new Term[] { in });
        this.substitutions = new ArrayList<>(substs);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(let ");
        for (Pair<VariableTerm,Term> pair : substitutions) {
            sb.append(pair.fst).append(" = ").append(pair.snd).append(", ");
        }
        sb.append(" in ").append(getInTerm()).append(")");
        return sb.toString();
    }

    private Term getInTerm() {
        return getSubterms().get(0);
    }

    @Override
    public <A, R> R accept(TermVisitor<A, R> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public List<Pair<VariableTerm, Term>> getSubstitutions() {
        return Collections.unmodifiableList(substitutions);
    }

}
