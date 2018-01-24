/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

public class LetTerm extends Term {

    private final List<Pair<VariableTerm, Term>> substitutions;

    public LetTerm(VariableTerm var, Term expression, Term in) throws TermBuildException {
        this(Collections.singletonList(new Pair<>(var, expression)), in);
    }

    public LetTerm(List<Pair<VariableTerm, Term>> substs, Term in) throws TermBuildException {
        super(in.getSort(), createSubterms(in, substs));
        this.substitutions = new ArrayList<>(substs);

        if (substs.isEmpty()) {
            throw new TermBuildException("Let term with empty variable assignment");
        }

        for (Pair<VariableTerm, Term> pair : substs) {
            VariableTerm fst = Objects.requireNonNull(pair.fst);
            Term snd = Objects.requireNonNull(pair.snd);
            if (!fst.getSort().equals(snd.getSort())) {
                throw new TermBuildException("Illegally typed assignment to " + fst);
            }
        }
    }

    public static Term[] createSubterms(Term in, List<Pair<VariableTerm, Term>> substs) {
        Term[] result = new Term[substs.size() + 1];
        result[0] = in;
        for (int i = 1; i < result.length; i++) {
            result[i] = substs.get(i-1).snd;
        }
        return result;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(let ")
            .append(Util.commatize(Util.map(substitutions, p -> p.fst.getName())))
            .append(" := ")
            .append(Util.commatize(Util.map(substitutions, p -> p.snd.toString())))
            .append(" :: ")
            .append(getTerm(0)).append(")");

        return sb.toString();
    }

    @Override
    public <A, R, E extends Exception>
            R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

    public List<Pair<VariableTerm, Term>> getSubstitutions() {
        return Collections.unmodifiableList(substitutions);
    }

    @Override
    public boolean equals(Object obj) {
        if (!super.equals(obj)) {
            return false;
        }

        LetTerm other = (LetTerm) obj;
        return substitutions.equals(other.substitutions);
    }

}
