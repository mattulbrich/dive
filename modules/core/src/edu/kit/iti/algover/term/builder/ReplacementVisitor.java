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

public class ReplacementVisitor<A> implements TermVisitor<A, Term, TermBuildException> {

    public VariableTerm visitBoundVariable(VariableTerm variableTerm, A arg) throws TermBuildException {
        return null;
    }

    private FunctionSymbol visitSubstitutionTarget(FunctionSymbol x) throws TermBuildException{
        return null;
    }

    @Override
    public Term visit(VariableTerm variableTerm, A arg) throws TermBuildException{
        return null;
    }

    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, A arg) throws TermBuildException{
        return null;
    }

    @Override
    public Term visit(QuantTerm quantTerm, A arg) throws TermBuildException {
        VariableTerm bv = visitBoundVariable(quantTerm.getBoundVar(), arg);
        Term matrix = quantTerm.getTerm(0).accept(this, arg);

        if(bv == null && matrix == null) {
            return quantTerm;
        }

        if(bv == null) {
            bv = quantTerm.getBoundVar();
        }

        if(matrix == null) {
            matrix = quantTerm.getTerm(0);
        }

        return new QuantTerm(quantTerm.getQuantifier(), bv, matrix);
    }

    @Override
    public Term visit(ApplTerm applTerm, A arg) throws TermBuildException {
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

        return new ApplTerm(applTerm.getFunctionSymbol(), newArgs);
    }

    @Override
    public Term visit(LetTerm letTerm, A arg) throws TermBuildException {
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

        return new LetTerm(newSubsts, subTerm);

    }

}
