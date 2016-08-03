/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Pair;

public class LetTerm extends Term {

    private final List<Pair<FunctionSymbol, Term>> substitutions;

    public LetTerm(FunctionSymbol var, Term expression, Term in) throws TermBuildException {
        this(Collections.singletonList(new Pair<>(var, expression)), in);
    }

    public LetTerm(List<Pair<FunctionSymbol, Term>> substs, Term in) throws TermBuildException {
        super(in.getSort(), new Term[] { in });
        this.substitutions = new ArrayList<>(substs);

        for (Pair<FunctionSymbol, Term> pair : substs) {
            if(pair.fst.getArity() != 0) {
                throw new TermBuildException("Assignment not non-constant");
            }
            if(!pair.fst.getResultSort().equals(pair.snd.getSort())) {
                throw new TermBuildException("Illegally typed assignment to " + pair.fst);
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(let ");
        for (Pair<FunctionSymbol,Term> pair : substitutions) {
            sb.append(pair.fst.getName()).append("=").append(pair.snd).append(", ");
        }
        // remove comma
        sb.setLength(sb.length()-2);
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

    public List<Pair<FunctionSymbol, Term>> getSubstitutions() {
        return Collections.unmodifiableList(substitutions);
    }

}
