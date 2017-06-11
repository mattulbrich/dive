/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

/**
 * The class can be extended to implement visitors which replace certain parts
 * of a term.
 *
 * Any replacement function can return <code>null</code> to indicate that the
 * subterm is not to be changed.
 *
 * Only if at least on of the sub calls returns a non-<code>null</code> value is
 * the resulting term rebuilt.
 *
 * @param <A>
 *            the generic type of the argument given to the visitor methods.
 */
public class ReplacementVisitor<A> implements TermVisitor<A, Term, TermBuildException> {

    /**
     * Visit bound variable within a quantifier.
     *
     * In an overriding class, return the replacement variable term or
     * <code>null</code> to keep the argument.
     *
     * @param variableTerm
     *            the variable term
     * @param arg
     *            the argument handed through the calls.
     * @return the replacement variable term or <code>null</code>
     * @throws TermBuildException
     *             may be thrown
     */
    public VariableTerm visitBoundVariable(VariableTerm variableTerm, A arg)
            throws TermBuildException {
        return null;
    }

    /**
     * Visit bound variable within a let expression.
     *
     * In an overriding class, return the replacement variable term or
     * <code>null</code> to keep the argument.
     *
     * @param x
     *            the variable term
     * @param arg
     *            the argument handed through the calls.
     * @return the replacement variable term or <code>null</code>
     * @throws TermBuildException
     *             may be thrown
     */
    public VariableTerm visitLetTarget(VariableTerm x, A arg) throws TermBuildException {
        return null;
    }

    /**
     * {@inheritDoc}
     *
     * Return <code>null</code> to keep the original term,
     * and return any other term if replacement is needed.
     */
    @Override
    public Term visit(VariableTerm variableTerm, A arg) throws TermBuildException {
        return null;
    }

    /**
     * {@inheritDoc}
     *
     * Return <code>null</code> to keep the original term,
     * and return any other term if replacement is needed.
     */
    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, A arg) throws TermBuildException {
        return null;
    }

    /**
     * {@inheritDoc}
     *
     * Return <code>null</code> to keep the original term,
     * and return any other term if replacement is needed.
     */
    @Override
    public Term visit(QuantTerm quantTerm, A arg) throws TermBuildException {
        VariableTerm bv = visitBoundVariable(quantTerm.getBoundVar(), arg);
        Term matrix = quantTerm.getTerm(0).accept(this, arg);

        if (bv == null && matrix == null) {
            return null;
        }

        if (bv == null) {
            bv = quantTerm.getBoundVar();
        }

        if (matrix == null) {
            matrix = quantTerm.getTerm(0);
        }

        return new QuantTerm(quantTerm.getQuantifier(), bv, matrix);
    }

    /**
     * {@inheritDoc}
     *
     * Return <code>null</code> to keep the original term,
     * and return any other term if replacement is needed.
     */
    @Override
    public Term visit(ApplTerm applTerm, A arg) throws TermBuildException {
        List<Term> newArgs = null;
        for (int i = 0; i < applTerm.countTerms(); i++) {
            Term t = applTerm.getTerm(i);
            Term subst = t.accept(this, arg);
            if (subst != null) {
                if (newArgs == null) {
                    newArgs = new ArrayList<>(applTerm.getSubterms());
                }
                newArgs.set(i, subst);
            }
        }

        if (newArgs == null) {
            return null;
        }

        return new ApplTerm(applTerm.getFunctionSymbol(), newArgs);
    }

    /**
     * {@inheritDoc}
     *
     * Return <code>null</code> to keep the original term,
     * and return any other term if replacement is needed.
     */
    @Override
    public Term visit(LetTerm letTerm, A arg) throws TermBuildException {
        List<Pair<VariableTerm, Term>> substs = letTerm.getSubstitutions();
        List<Pair<VariableTerm, Term>> newSubsts = null;
        for (int i = 0; i < substs.size(); i++) {
            VariableTerm var = substs.get(i).fst;
            VariableTerm substVar = visitLetTarget(var, arg);

            Term term = substs.get(i).snd;
            Term substTerm = term.accept(this, arg);

            if (substTerm != null || substVar != null) {
                if (newSubsts == null) {
                    newSubsts = new ArrayList<>(substs);
                }
                if (substVar == null) {
                    substVar = var;
                }
                if (substTerm == null) {
                    substTerm = term;
                }
                newSubsts.set(i, new Pair<VariableTerm, Term>(substVar, substTerm));
            }
        }

        Term subTerm = letTerm.getTerm(0).accept(this, arg);

        if (newSubsts == null && subTerm == null) {
            return null;
        }

        if (subTerm == null) {
            subTerm = letTerm.getTerm(0);
        }

        if (newSubsts == null) {
            newSubsts = substs;
        }

        return new LetTerm(newSubsts, subTerm);
    }

}
