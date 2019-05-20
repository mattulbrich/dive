/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.HashMap;
import java.util.Map;

import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.HistoryMap;
import edu.kit.iti.algover.util.Pair;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * The Class LetInlineVisitor walks over a term and reduces all {@link LetTerm}s
 * by replacing the bound variables by their replacement in the argument term.
 *
 * The resulting Term does not have {@link LetTerm}s embedded anymore.
 *
 * The static method {@link #inline(Term)} can be used as entry point.
 *
 * @author mulbrich
 *
 * @see edu.kit.iti.algover.rules.impl.SubstitutionVisitor
 */
public class LetInlineVisitor extends
        ReplacementVisitor<HistoryMap<VariableTerm, Term>> {


    /**
     * Inline all {@link LetTerm}s in a term.
     *
     * @param term
     *            the non-<code>null</code> term to walk over
     * @return an equivalent term w/o {@link LetTerm}s. It may be identical to
     *         to <code>term</code>.
     * @throws TermBuildException
     *             if the term cannot be replaced (should actually not come up)
     */
    public static Term inline(@NonNull Term term) throws TermBuildException {
        return inline(null, term);
    }

    /**
     * Inline all {@link LetTerm}s in a term.
     *
     * @param term
     *            the non-{@code null} term to walk over
     * @param termMap
     *            the (optional) map which is to be updated with new term objects
     * @return an equivalent term w/o {@link LetTerm}s. It may be identical to
     *         to {@code term}.
     * @throws TermBuildException
     *             if the term cannot be replaced (should actually not come up)
     */
    public static Term inline(@Nullable Map<Term,?> termMap, @NonNull Term term) throws TermBuildException {
        LetInlineVisitor visitor = new LetInlineVisitor();
        visitor.setTermMap(termMap);
        Term result = term.accept(visitor, new HistoryMap<>(new HashMap<>()));

        if (result == null) {
            result = term;
        }

        return result;
    }

    @Override
    public Term visit(VariableTerm variableTerm, HistoryMap<VariableTerm, Term> lets)
            throws TermBuildException {
        Term subst = lets.get(variableTerm);
        if (subst != null) {
            return subst;
        } else {
            return super.visit(variableTerm, lets);
        }
    }

    @Override
    public Term visit(LetTerm letTerm, HistoryMap<VariableTerm, Term> lets)
            throws TermBuildException {
        Map<VariableTerm, Term> newLets = new HashMap<>();
        for (Pair<VariableTerm, Term> ass : letTerm.getSubstitutions()) {
            VariableTerm f = ass.fst;
            Term replacement = ass.snd.accept(this, lets);
            if (replacement == null) {
                replacement = ass.snd;
            }
            newLets.put(f, replacement);
        }

        int rewindPos = lets.getHistory();
        lets.putAll(newLets);
        Term inner = letTerm.getTerm(0).accept(this, lets);
        lets.rewindHistory(rewindPos);

        if (inner == null) {
            return letTerm.getTerm(0);
        } else {
            return inner;
        }
    }

    @Override
    public Term visit(QuantTerm quantTerm, HistoryMap<VariableTerm, Term> lets) throws TermBuildException {
        VariableTerm var = quantTerm.getBoundVar();

        HistoryMap<VariableTerm, Term> newLets = new HistoryMap<>(lets);
        newLets.remove(var);

        Term inner = quantTerm.getTerm(0).accept(this, newLets);
        if(inner == null) {
            return quantTerm;
        } else {
            QuantTerm result = new QuantTerm(quantTerm.getQuantifier(), var, inner);
            updateMap(quantTerm, result);
            return result;
        }
    }
}
