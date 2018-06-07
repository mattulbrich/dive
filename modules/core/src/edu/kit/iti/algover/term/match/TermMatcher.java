/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;


import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Triple;

import java.util.List;
import java.util.stream.Collectors;

/**
 * This is the class that contains the actual algorithm that implements term
 * matching.
 *
 * <p>Vital in its operation is the visitor class {@link Visitor} that does the
 * actual work.</p>
 *
 * <p>The visitor uses {@link Triple}s of some kind. This is since the {@link
 * Visitor} interface only allows for single argument.</p>
 *
 * @author Mattias Ulbrich
 */
public class TermMatcher {

    private class Visitor
            implements TermVisitor<Triple<Term, Matching, SubtermSelector>,
                                   ImmutableList<Matching>, MatchException> {

        /*
         * If schema variable has a name like "?x":
         *   If it is instantiated: Verify that the instantiation is equal
         *          to comparison term
         *   If it is not instantiated: Instantiate it with the comparison term.
         * If it is unnamed, add the unnamed assignment to the matching.
         */
        @Override
        public ImmutableList<Matching> visit(SchemaVarTerm schemaVarTerm,
                                             Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {

            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            if(schemaVarTerm.hasName()) {
                MatchingEntry entry = m.get(schemaVarTerm.getName());
                if(entry == null) {
                    return ImmutableList.single(m.add(schemaVarTerm.getName(), conc, sel));
                } else {
                    Term alreadyThere = entry.getValue();
                    if(!alreadyThere.equals(conc)) {
                        throw new MatchException(schemaVarTerm, conc);
                    } else {
                        return ImmutableList.single(m);
                    }
                }
            } else {
                return ImmutableList.single(m.addUnnamed(conc, sel));
            }
        }

        /*
         * a "...term..." is matched by matching the inner term recursively
         * against all substerms of the comparison term.
         *
         * This may lead to several Matchings, not just one.
         */
        @Override
        public ImmutableList<Matching> visit(SchemaOccurTerm occurTerm,
                                             Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {

            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            Term innerTerm = occurTerm.getTerm(0);

            ImmutableList<Matching> result;
            try {
                result = innerTerm.accept(this, arg);
                result = result.map(x -> x.addEllipsis(conc, sel));
            } catch(MatchException ex) {
                // it's ok not to match!
                result = ImmutableList.nil();
            }

            for(int i = 0; i < conc.countTerms(); i++) {
                Term subTerm = conc.getTerm(i);
                SubtermSelector subSel = new SubtermSelector(sel, i);
                    result = result.appendAll(occurTerm.accept(this, new Triple<>(subTerm, m, subSel)));
            }

            return result;
        }

        /*
         * Variables must be euqal.
         */
        @Override
        public ImmutableList<Matching> visit(VariableTerm varTerm,
                                             Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;

            if(varTerm.equals(conc)) {
                return ImmutableList.single(m);
            } else {
                throw new MatchException(varTerm, conc);
            }
        }

        /*
         * Function applications must be on the same function symbol and
         * recursively be matchable.
         */
        @Override
        public ImmutableList<Matching> visit(ApplTerm applTerm, Triple<Term, Matching, SubtermSelector> arg) throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            if(applTerm.equals(conc)) {
                return ImmutableList.single(m);
            }

            if(!(conc instanceof ApplTerm)) {
                throw new MatchException(applTerm, conc);
            }

            ApplTerm applTerm2 = (ApplTerm) conc;

            FunctionSymbol f1 = applTerm.getFunctionSymbol();
            FunctionSymbol f2 = applTerm2.getFunctionSymbol();

            if (!f1.equals(f2)) {
                throw new MatchException(applTerm, conc);
            }

            ImmutableList<Matching> matchings = ImmutableList.single(m);
            for(int i = 0; i < f1.getArity(); i++) {
                Term subSchem = applTerm.getTerm(i);
                Term subConc = conc.getTerm(i);
                SubtermSelector subSel = new SubtermSelector(sel, i);
                matchings = matchings.flatMap(x ->
                    subSchem.accept(this, new Triple<>(subConc, x, subSel)));
            }

            return matchings;
        }

        /*
         * For a quantifier, the type and the variable must be the same and
         * the matrix must be matchable.
         *
         * TODO In the future have some notion of schematic bound variable.
         */
        @Override
        public ImmutableList<Matching> visit(QuantTerm quantTerm,
                                             Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            if(quantTerm.equals(conc)) {
                return ImmutableList.single(m);
            }

            if(!(conc instanceof QuantTerm)) {
                throw new MatchException(quantTerm, conc);
            }

            QuantTerm quantTerm2 = (QuantTerm) conc;

            Quantifier f1 = quantTerm.getQuantifier();
            Quantifier f2 = quantTerm2.getQuantifier();

            if(f1 != f2) {
                throw new Error();
            }

            // TODO allow matching bound variable, too.
            if(!quantTerm.getBoundVar().equals(quantTerm2.getBoundVar())) {
                throw new MatchException(quantTerm, conc);
            }

            Term subSchem = quantTerm.getTerm(0);
            Term subConc = conc.getTerm(0);
            SubtermSelector subSel = new SubtermSelector(sel, 0);

            return subSchem.accept(this, new Triple<>(subConc, m, subSel));
        }

        /*
         * Two let terms match iff:
         * * the variables are in the same order, have the same name and the values match
         * * the in term match
         */
        @Override
        public ImmutableList<Matching> visit(LetTerm letTerm, Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {
            Matching m = arg.snd;

            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            //shortcuts
            if (letTerm.equals(conc)) {
                return ImmutableList.single(m);
            }
            if (!(conc instanceof LetTerm)) {
                throw new MatchException(letTerm, conc);
            }
            LetTerm concreteLet = (LetTerm) conc;


            //match IN term
            Term subSchem = letTerm.getTerm(0);
            Term subConc = conc.getTerm(0);
            SubtermSelector subSel = new SubtermSelector(sel, 0);
            ImmutableList<Matching> matchings = subSchem.accept(this, new Triple<>(subConc, m, subSel));
            if (matchings.isEmpty()) {
                throw new MatchException(subSchem, subConc);
            }

            //substitution variable handling: check that the variable names are the same, in the same order and may either have the same sort or UNTYPED
            List<VariableTerm> varsConcrete = concreteLet.getSubstitutions().stream().map(variableTermTermPair -> variableTermTermPair.getFst()).collect(Collectors.toList());
            List<VariableTerm> varsSchema = letTerm.getSubstitutions().stream().map(variableTermTermPair -> variableTermTermPair.getFst()).collect(Collectors.toList());

            for (int i = 0; i < varsConcrete.size(); i++) {
                VariableTerm concreteVariableTerm = varsConcrete.get(i);
                VariableTerm schemaVariableTerm = varsSchema.get(i);

                //check the names and the sorts
                if (!concreteVariableTerm.getName().equals(schemaVariableTerm.getName())) {
                    throw new MatchException(schemaVariableTerm, concreteVariableTerm);
                } else {
                    if (schemaVariableTerm.getSort() != Sort.UNTYPED_SORT && !schemaVariableTerm.getSort().equals(concreteVariableTerm.getSort())) {
                        throw new MatchException(schemaVariableTerm, concreteVariableTerm);
                    }
                }

            }

            //match the substitutions
            for (int i = 0; i < concreteLet.getSubstitutions().size(); i++) {
                Term substSchem = letTerm.getSubstitutions().get(i).getSnd();
                Term substConc = ((LetTerm) conc).getSubstitutions().get(i).getSnd();
                SubtermSelector substSel = new SubtermSelector(sel, i);
                matchings = matchings.flatMap(x ->
                        substSchem.accept(this, new Triple<>(substConc, x, substSel)));
            }

            return matchings;


        }
    }

  /*   TermMatcher() {
    polaritay option

    }

   TermMatcher(TermSelector.SequentPolarity polarity, int termNo) {
        this.polarity = polarity;
        this.termNo = termNo;
    }*/

    /**
     * Match a schematic term against another term.
     *
     * <p> The result may be 0, 1 or more {@link Matching}s. This is since the
     * ellipsis operator may match differently at different points. </p>
     *
     * <p> The second term will in most cases be a term w/o schematic entities.
     * This is not strictly required, however. But matching happens only in the
     * first argument. Hence, {@code ?x} matches against {@code 42}, but not
     * {@code 42} does not match against {@code ?x}. </p>
     *
     * @param schematicTerm the term with the schema entities
     * @param concreteTerm  the term to match against
     * @return a list of all matchings which unify the two arguments.
     */
    public ImmutableList<Matching> match(Term schematicTerm, Term concreteTerm) {
        return match(schematicTerm, concreteTerm, Matching.emptyMatching());
    }

    /**
     * Match a schematic term against another term at any position within the
     * term.
     *
     * <p> The result may be 0, 1 or more {@link Matching}s. This is since the
     * ellipsis operator may match differently at different points. </p>
     *
     * <p> The second term will in most cases be a term w/o schematic entities.
     * This is not strictly required, however. But matching happens only in the
     * first argument. Hence, {@code ?x} matches against {@code 42}, but not
     * {@code 42} does not match against {@code ?x}. </p>
     *
     * <p>Technically, a {@link SchemaOccurTerm} (ellipsis) is used to model
     * the schematic term to match.</p>
     *
     * @param schematicTerm the term with the schema entities
     * @param concreteTerm  the term to match against
     * @return a list of all matchings which unify the two arguments.
     */
    public ImmutableList<Matching> matchOccurrences(Term schematicTerm, Term concreteTerm) {
        return match(new SchemaOccurTerm(schematicTerm), concreteTerm);
    }

    /**
     * Match a schematic term against another term.
     *
     * <p> The result may be 0, 1 or more {@link Matching}s. This is since the
     * ellipsis operator may match differently at different points. </p>
     *
     * <p> The second term will in most cases be a term w/o schematic entities.
     * This is not strictly required, however. But matching happens only in the
     * first argument. Hence, {@code ?x} matches against {@code 42}, but not
     * {@code 42} does not match against {@code ?x}. </p>
     *
     * <p>This method does not start with an empty matching context but with the
     * one specified in m.</p>
     *
     * @param schem the term with the schema entities
     * @param conc  the term to match against
     * @param m     the matching to begin from.
     * @return a list of all matchings which unify the two arguments.
     */
    public ImmutableList<Matching> match(Term schem, Term conc, Matching m) {
        try {
            return schem.accept(new Visitor(), new Triple<>(conc, m, new SubtermSelector()));
        } catch (MatchException e) {
            // The exception indicates that they do not match
            return ImmutableList.nil();
        }
    }



}
