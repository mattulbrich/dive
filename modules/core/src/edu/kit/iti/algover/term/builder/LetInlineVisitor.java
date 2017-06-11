/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

public class LetInlineVisitor extends
        ReplacementVisitor<ImmutableList<Pair<VariableTerm, Term>>> {

    private static final ImmutableList<Pair<VariableTerm, Term>> NIL = ImmutableList.<Pair<VariableTerm, Term>>nil();

    @Override
    public Term visit(VariableTerm variableTerm, ImmutableList<Pair<VariableTerm, Term>> lets) throws TermBuildException {
        Term subst = getSubst(lets, variableTerm);
        if(subst != null) {
            return subst;
        } else {
            return super.visit(variableTerm, lets);
        }
    }

    private Term getSubst(ImmutableList<Pair<VariableTerm, Term>> lets, VariableTerm f) {
        while(lets != NIL) {
            if(lets.getHead().fst == f) {
                return lets.getHead().snd;
            }
            lets = lets.getTail();
        }
        return null;
    }

    @Override
    public Term visit(LetTerm letTerm, ImmutableList<Pair<VariableTerm, Term>> lets) throws TermBuildException {
        ImmutableList<Pair<VariableTerm, Term>> oldLets = lets;
        for (Pair<VariableTerm, Term> ass : letTerm.getSubstitutions()) {
            VariableTerm f = ass.fst;
            Term t = ass.snd.accept(this, oldLets);
            lets = lets.append(new Pair<>(f, t));
        }

        Term inner = letTerm.getTerm(0).accept(this, lets);

        return inner;
    }
}
