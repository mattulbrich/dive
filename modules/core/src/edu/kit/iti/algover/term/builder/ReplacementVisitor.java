/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

public class ReplacementVisitor<A> implements TermVisitor<A, Term> {

    public Term applyTo(Term term, A arg) throws TermBuildException {
        try {
            return term.accept(this, arg);
        } catch(RuntimeException e) {
            Throwable cause = e.getCause();
            if(cause instanceof TermBuildException) {
                throw (TermBuildException)cause;
            } else
                throw e;
        }
    }

    public VariableTerm visitBoundVariable(VariableTerm variableTerm, A arg) {
        return null;
    }

    private FunctionSymbol visitSubstitutionTarget(FunctionSymbol x) {
        return null;
    }

    @Override
    public Term visit(VariableTerm variableTerm, A arg) {
        return null;
    }

    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, A arg) {
        return null;
    }

    @Override
    public Term visit(QuantTerm quantTerm, A arg) {
        return null;
    }

    @Override
    public Term visit(ApplTerm applTerm, A arg) {
        List<Term> newArgs = null;
        for (int i = 0; i < applTerm.countTerms(); i++) {
            Term t = applTerm.getTerm(i);
            Term subst = t.accept(this, arg);
            if(subst != null) {
                if(newArgs == null) {
                    newArgs = new ArrayList<>(applTerm.getSubterms());
                }
                newArgs.set(i, subst);
            }
        }

        if(newArgs == null) {
            return null;
        }

        try {
            return new ApplTerm(applTerm.getFunctionSymbol(), newArgs);
        } catch (TermBuildException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term visit(LetTerm letTerm, A arg) {
        List<Pair<FunctionSymbol, Term>> substs = letTerm.getSubstitutions();
        List<Pair<FunctionSymbol, Term>> newSubsts = null;
        for (int i = 0; i < substs.size(); i++) {
            FunctionSymbol x = substs.get(i).fst;
            FunctionSymbol substX = visitSubstitutionTarget(x);

            Term t = substs.get(i).snd.getTerm(i);
            Term subst = t.accept(this, arg);

            if(subst != null || substX != null) {
                if(newSubsts == null) {
                    newSubsts = new ArrayList<>(substs);
                }
                newSubsts.set(i, new Pair<FunctionSymbol, Term>(substX, subst));
            }
        }

        Term subTerm = letTerm.getTerm(0).accept(this, arg);

        if(newSubsts == null && subTerm == null) {
            return null;
        }

        if(subTerm == null) {
            subTerm = letTerm.getTerm(0);
        }

        try {
            return new LetTerm(newSubsts, subTerm);
        } catch (TermBuildException e) {
            throw new RuntimeException(e);
        }

    }

}
