/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;
import nonnull.NonNull;

/**
 * The Class ReplaceVisitor is used to replace one subterm identified by a
 * {@link SubtermSelector} with another term.
 *
 * The method recursively descends into the term data structure, replaces the
 * relevant term and rebuilds teh term data structure around it.
 *
 * @author mattias ulbrich
 */
public class ReplaceVisitor  {

    private static class RebuiltVisitor implements TermVisitor<List<Term>, Term, TermBuildException> {

        @Override
        public Term visit(VariableTerm variableTerm, List<Term> arg) throws TermBuildException {
            assert arg.size() == 0 : "No parameters for variables";
            return variableTerm;
        }

        @Override
        public Term visit(SchemaVarTerm schemaVarTerm, List<Term> arg) throws TermBuildException {
            assert arg.size() == 0 : "No parameters for variables";
            return schemaVarTerm;
        }

        @Override
        public Term visit(QuantTerm quantTerm, List<Term> arg) throws TermBuildException {
            assert arg.size() == 1 : "There must be one argument for quantifiers";
            return new QuantTerm(quantTerm.getQuantifier(), quantTerm.getBoundVar(), arg.get(0));
        }

        @Override
        public Term visit(ApplTerm applTerm, List<Term> arg) throws TermBuildException {
            return new ApplTerm(applTerm.getFunctionSymbol(), arg);
        }

        @Override
        public Term visit(LetTerm letTerm, List<Term> arg) throws TermBuildException {
            List<Pair<VariableTerm, Term>> subs = new ArrayList<>();
            List<Pair<VariableTerm, Term>> oldSubs = letTerm.getSubstitutions();
            assert oldSubs.size() == arg.size() - 1;
            for(int i = 1; i < arg.size(); ++i) {
                subs.add(new Pair<>(oldSubs.get(i - 1).fst, arg.get(i)));
            }
            return new LetTerm(subs, arg.get(0));
        }

    }

    private static final RebuiltVisitor REBUILD_VISITOR = new RebuiltVisitor();

    /**
     * Replace a suberm in a term data structure with another term.
     *
     * @param topTerm
     *            the term in which the replacement is to happen
     * @param selector
     *            the selector telling which position is to be replaced
     * @param replacement
     *            the replacement term
     * @return the term which is the same as topTerm but with the term at
     *         selector replaced by replacement
     * @throws TermBuildException
     *             thrown if typing rules are violated by the substitution.
     */
    public static Term replace(@NonNull Term topTerm,
            @NonNull SubtermSelector selector,
            @NonNull Term replacement) throws TermBuildException {
        return replace(topTerm, selector, replacement, 0);
    }

    private static Term replace(Term term, SubtermSelector selector, Term replacement, int pos) throws TermBuildException {
        if(pos >= selector.getDepth()) {
            return replacement;
        }

        int index = selector.getSubtermNumber(pos);
        List<Term> children = new ArrayList<>(term.getSubterms());
        children.set(index, replace(children.get(index), selector, replacement, pos + 1));

        Term rebuilt = term.accept(REBUILD_VISITOR, children);

        return rebuilt;
    }

}
