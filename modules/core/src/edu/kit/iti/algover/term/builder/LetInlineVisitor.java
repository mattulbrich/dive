/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

public class LetInlineVisitor extends
        ReplacementVisitor<ImmutableList<Pair<FunctionSymbol, Term>>> {

    private static final ImmutableList<Pair<FunctionSymbol, Term>> NIL = ImmutableList.<Pair<FunctionSymbol, Term>>nil();

    @Override
    public Term visit(ApplTerm applTerm, ImmutableList<Pair<FunctionSymbol, Term>> lets) {
        if(applTerm.countTerms() == 0) {
            FunctionSymbol f = applTerm.getFunctionSymbol();
            return getSubst(lets, f);
        } else {
            return super.visit(applTerm, lets);
        }
    }

    private Term getSubst(ImmutableList<Pair<FunctionSymbol, Term>> lets, FunctionSymbol f) {
        while(lets != NIL) {
            if(lets.getHead().fst == f) {
                return lets.getHead().snd;
            }
            lets = lets.getTail();
        }
        return null;
    }

    @Override
    public Term visit(LetTerm letTerm, ImmutableList<Pair<FunctionSymbol, Term>> lets) {
        ImmutableList<Pair<FunctionSymbol, Term>> oldLets = lets;
        for (Pair<FunctionSymbol, Term> ass : letTerm.getSubstitutions()) {
            FunctionSymbol f = ass.fst;
            Term t = ass.snd.accept(this, oldLets);
            lets = lets.append(new Pair<>(f, t));
        }

        Term inner = letTerm.getTerm(0).accept(this, lets);

        return inner;
    }
}
