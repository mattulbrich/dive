/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.ImmutableSet;
import edu.kit.iti.algover.util.Immutables;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

/**
 * The methods in this class can be used to make sure that a term has no
 * name clashes.
 *
 * A bound variable must not hide a used constant. In "let x := 3 :: x==x",
 * it must not be that the last x is not the variable, but a constant
 * (coincidently named x).
 *
 * One important consequence of the normalisation process is that
 * normalised terms are meant to have the property that
 * <code>
 *     TermParser.parse(symbols, term.toString()).equals(term)
 * </code>
 * is true for all (non-null) terms if the symbol table is complete.
 *
 * In the past there were a few incidences with non-normalised formulas
 * on the sequent.
 *
 * It is therefore checked by an assertion that any ProofFormula contains a
 * normalised formula.
 *
 * If required at some point., the {@link #normalise(Term)} method can be
 * implemented which renames variables to ensure normalised terms.
 *
 * @author mattias ulbrich
 */
public class AlphaNormalisation {

    public static @NonNull Term normalise(@NonNull Term term) {
        throw new Error("Not yet implemented. Implement this when needed");
    }

    public static boolean isNormalised(@NonNull Term term) {
        NameDetector nd = new NameDetector();
        term.accept(nd, null);
        for (Entry<LetTerm, ImmutableSet<Term>> en : nd.clashMap.entrySet()) {
            LetTerm letTerm = en.getKey();
            ImmutableSet<Term> clashCandidates = en.getValue();
            List<VariableTerm> boundVars = Util.map(letTerm.getSubstitutions(), p -> p.fst);
            for (VariableTerm boundVar : boundVars) {
                if(hasClash(boundVar, clashCandidates)) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean hasClash(VariableTerm var, ImmutableSet<Term> clashCandidates) {
        String varStr = var.getName();
        for (Term candidate : clashCandidates) {
            String candStr = candidate.toString();
            if (candStr.equals(varStr) && !candidate.equals(var)) {
                return true;
            }
        }
        return false;
    }


    private static class NameDetector extends
            DefaultTermVisitor<Void, ImmutableSet<Term>, NoExceptions> {

        private Map<LetTerm, ImmutableSet<Term>> clashMap = new IdentityHashMap<>();

        @Override
        protected ImmutableSet<Term> defaultVisit(Term term, Void arg) {
            ImmutableSet<Term> result = Immutables.emptySet();
            for (Term subterm : term.getSubterms()) {
                result = result.addAll(subterm.accept(this, arg));
            }
            return result;
        }

        @Override
        public ImmutableSet<Term> visit(ApplTerm term, Void arg) {
            ImmutableSet<Term> result = defaultVisit(term, arg);
            if(term.countTerms() == 0) {
                // it is a constant.
                result = result.add(term);
            }
            return result;
        }

        @Override
        public ImmutableSet<Term> visit(VariableTerm term, Void arg) {
            return Immutables.setOf(term);
        }

        @Override
        public ImmutableSet<Term> visit(LetTerm term, Void arg) {

            ImmutableSet<Term> result = Immutables.emptySet();
            int termNo = 0;
            for (Term subterm : term.getSubterms()) {
                result = result.addAll(subterm.accept(this, arg));
                if(termNo == 0) {
                    result = result.removeAll(Util.map(term.getSubstitutions(), x->x.fst));
                    clashMap.put(term, result);
                }
                termNo ++;
            }
            return result;
        }

        @Override
        public ImmutableSet<Term> visitSchemaTerm(SchemaTerm schemaTerm, Void arg) {
            return defaultVisit(schemaTerm, arg);
        }
    }
}
