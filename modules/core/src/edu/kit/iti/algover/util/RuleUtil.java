/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.match.TermMatcher;

import java.util.*;
import java.util.function.Predicate;

/**
 * Utilities for implementing Proof Rules.
 * <p>
 * Term matching: Always looks for the first match and then stops search.
 *
 * @author philipp
 */
public class RuleUtil {


    /**
     * Tries to match the first Term in the whole sequent, from top to bottom.
     * Starts with the antecedent, goes top to bottom of terms.
     *
     * @param predicate the predicate that the term you are looking for should match. For finding specific terms, use term::equals
     * @param sequent   the sequent to look for the term.
     * @return Either a filled optional with the first matching TermSelector inside, or Optional.empty() when none could be found.
     */
    public static Optional<TermSelector> matchSubtermInSequent(Predicate<Term> predicate, Sequent sequent) {
        Optional<TermSelector> inAntecedent = matchSubtermInPolarity(TermSelector.SequentPolarity.ANTECEDENT, predicate, sequent.getAntecedent());
        if (inAntecedent.isPresent()) {
            return inAntecedent;
        }
        return matchSubtermInPolarity(TermSelector.SequentPolarity.SUCCEDENT, predicate, sequent.getSuccedent());
    }

    /**
     * Finds all matches of the given Term in the whole sequent, from top to bottom.
     * Starts with the antecedent, goes top to bottom of terms.
     *
     * @param predicate the predicate that the term you are looking for should match. For finding specific terms, use term::equals
     * @param sequent   the sequent to look for the term.
     * @return A List of TermSelectors pointing to the matches found.
     */
    public static List<TermSelector> matchSubtermsInSequent(Predicate<Term> predicate, Sequent sequent) {
        List<TermSelector> inAntecedent = matchSubtermsInPolarity(TermSelector.SequentPolarity.ANTECEDENT, predicate, sequent.getAntecedent());
        inAntecedent.addAll(matchSubtermsInPolarity(TermSelector.SequentPolarity.SUCCEDENT, predicate, sequent.getSuccedent()));
        return inAntecedent;
    }

    /**
     * Finds a Subterm in only one of the polarities of a sequent. So if you are looking for a <strong>sub</strong>term
     * (i.e. it may be nested deep inside other terms) in the succedent, then use for example:
     * <p>
     * <code>matchSubtermInPolarity(SequentPolarity.SUCCEDENT, termImLookingFor::equals, sequent.getSuccedent())</code>
     * <p>
     * .
     *
     * @param polarity  the SequentPolarity you are looking for in. Used for constructing the appropriate TermSelector.
     * @param predicate the predicate that the term has to match. For finding specific terms, use specificTerm::equals
     * @param formulas  either the antecedent or succedent of a sequent (i.e. sequent.getAntedecent() or ...).
     *                  Sublists of that result in incorrect indices in the TermSelector!
     * @return Either a filled optional with the first matching TermSelector inside, or Optional.empty() when none could be found.
     */
    public static Optional<TermSelector> matchSubtermInPolarity(
            TermSelector.SequentPolarity polarity, Predicate<Term> predicate, List<ProofFormula> formulas) {
        for (int i = 0; i < formulas.size(); i++) {
            Optional<SubtermSelector> optionalFind = matchSubterm(predicate, formulas.get(i).getTerm());
            if (optionalFind.isPresent()) {
                final int idx = i;
                return optionalFind.map(subtermSelector ->
                        selectorInSequentAt(polarity, idx, subtermSelector));
            }
        }
        return Optional.empty();
    }

    /**
     * Finds all Subterms in only one of the polarities of a sequent. So if you are looking for a <strong>sub</strong>term
     * (i.e. it may be nested deep inside other terms) in the succedent, then use for example:
     * <p>
     * <code>matchSubtermInPolarity(SequentPolarity.SUCCEDENT, termImLookingFor::equals, sequent.getSuccedent())</code>
     * <p>
     * .
     *
     * @param polarity  the SequentPolarity you are looking for in. Used for constructing the appropriate TermSelector.
     * @param predicate the predicate that the term has to match. For finding specific terms, use specificTerm::equals
     * @param formulas  either the antecedent or succedent of a sequent (i.e. sequent.getAntedecent() or ...).
     *                  Sublists of that result in incorrect indices in the TermSelector!
     * @return A List of TermSelectors pointing to the matches found.
     */
    public static List<TermSelector> matchSubtermsInPolarity(
            TermSelector.SequentPolarity polarity, Predicate<Term> predicate, List<ProofFormula> formulas) {
        List<TermSelector> res = new ArrayList<>();
        for (int i = 0; i < formulas.size(); i++) {
            List<SubtermSelector> list = matchSubterms(predicate, formulas.get(i).getTerm());
            for(SubtermSelector sts : list) {
                res.add(new TermSelector(new TermSelector(polarity, i), sts));
            }
        }
        return res;
    }

    /*
     * From a SubtermSelector selector, creates something like new TermSelector(polarity, index, selector.getPath()).
     */
    private static TermSelector selectorInSequentAt(TermSelector.SequentPolarity polarity, int index, SubtermSelector selector) {
        int path[] = new int[selector.getPath().size()];
        for (int i = 0; i < path.length; i++) {
            path[i] = selector.getPath().get(i);
        }
        return new TermSelector(polarity, index, path);
    }

    /**
     * Shorthand for <code>{@link #matchTopLevelIndex(Predicate, List) matchTopLevel}(predicate, sequent.getAntecedent())</code>
     */
    public static Optional<Integer> matchTopLevelInAntedecent(Predicate<Term> predicate, Sequent sequent) {
        return matchTopLevelIndex(predicate, sequent.getAntecedent());
    }

    /**
     * Tries to find a term that matches the given predicate in the given term arbitrarily deeply nested (recursively),
     * and, if found, returns a SubtermSelector.
     *
     * @param predicate    the predicate that the term has to match. If you're looking for a specificTerm, use <code>specificTerm::equals</code>.
     * @param topLevelTerm
     * @return Either a filled optional with the first matching SubtermSelector inside, or Optional.empty() when none could be found.
     */
    public static Optional<SubtermSelector> matchSubterm(Predicate<Term> predicate, Term topLevelTerm) {
        return matchSubtermAccum(new SubtermSelector(), predicate, topLevelTerm);
    }

    /**
     * Finds all terms that matche the given predicate in the given term arbitrarily deeply nested (recursively),
     * and returns a list of SubtermSelectors.
     *
     * @param predicate    the predicate that the term has to match. If you're looking for a specificTerm, use <code>specificTerm::equals</code>.
     * @param topLevelTerm
     * @return A List of TermSelectors pointing to the matches found.
     */
    public static List<SubtermSelector> matchSubterms(Predicate<Term> predicate, Term topLevelTerm) {
        return matchSubtermsAccum(new SubtermSelector(), predicate, topLevelTerm);
    }

    /**
     * Shorthand for <code>{@link #matchTopLevelIndex(Predicate, List) matchTopLevel}(predicate, sequent.getSuccedent())</code>
     */
    public static Optional<Integer> matchTopLevelInSuccedent(Predicate<Term> predicate, Sequent sequent) {
        return matchTopLevelIndex(predicate, sequent.getSuccedent());
    }

    /**
     * Matches only Top-Level terms. If you are looking for arbitrarily-deeply nested terms,
     * use {@link #matchSubtermInPolarity(TermSelector.SequentPolarity, Predicate, List)}.
     *
     * @param predicate the predicate that the term has to fulfill. If you're looking for specific terms, use specificTerm::equals
     * @param formulas  either the antecedent or succedent of a sequent: {@link Sequent#getAntecedent()} or {@link Sequent#getSuccedent()}.
     * @return Either an Optional of the index of the first matched top-level term, or Optional.empty() if none could be found.
     */
    public static Optional<Integer> matchTopLevelIndex(Predicate<Term> predicate, List<ProofFormula> formulas) {
        for (int i = 0; i < formulas.size(); i++) {
            if (predicate.test(formulas.get(i).getTerm())) {
                return Optional.of(i);
            }
        }
        return Optional.empty();
    }

    public static Optional<TermSelector> matchTopLevel(Predicate<Term> predicate, Sequent sequent) {
        Optional<TermSelector> antecedent =
                matchTopLevelInAntedecent(predicate, sequent).map(idx -> new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, idx));
        if (antecedent.isPresent()) {
            return antecedent;
        }
        return matchTopLevelInSuccedent(predicate, sequent).map(idx -> new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, idx));
    }

    /*
     * This just tail-recursively (even though this does not optimize in the jvm yet) looks for a matching predicate inside the terms
     * subterms (and also the term itself), with the assumption, that term is already a subterm, that can be selected via the given
     * "alreadySelected" SubtermSelector.
     */
    private static Optional<SubtermSelector> matchSubtermAccum(SubtermSelector alreadySelected, Predicate<Term> predicate, Term term) {
        if (predicate.test(term)) {
            return Optional.of(alreadySelected);
        } else {
            for (int subtermIndex = 0; subtermIndex < term.getSubterms().size(); subtermIndex++) {
                Optional<SubtermSelector> foundSelector =
                        matchSubtermAccum(
                                new SubtermSelector(alreadySelected, subtermIndex),
                                predicate,
                                term.getTerm(subtermIndex));
                if (foundSelector.isPresent()) {
                    return foundSelector;
                }
            }
            return Optional.empty();
        }
    }

    /*
     * This just tail-recursively (even though this does not optimize in the jvm yet) looks for a matching predicate inside the terms
     * subterms (and also the term itself), with the assumption, that term is already a subterm, that can be selected via the given
     * "alreadySelected" SubtermSelector.
     */
    private static List<SubtermSelector> matchSubtermsAccum(SubtermSelector alreadySelected, Predicate<Term> predicate, Term term) {
        List<SubtermSelector> res = new ArrayList<>();
        if (predicate.test(term)) {
            res.add(alreadySelected);
        } else {
            for (int subtermIndex = 0; subtermIndex < term.getSubterms().size(); subtermIndex++) {
                Optional<SubtermSelector> foundSelector =
                        matchSubtermAccum(
                                new SubtermSelector(alreadySelected, subtermIndex),
                                predicate,
                                term.getTerm(subtermIndex));
                if (foundSelector.isPresent()) {
                    res.add(foundSelector.get());
                }
            }
        }
        return res;
    }

    public static TermSelector.SequentPolarity getTruePolarity(TermSelector ts, Sequent s) throws RuleException {
        if(ts.isAntecedent() && getNumNegations(ts, s, 0) % 2 == 0) {
            return TermSelector.SequentPolarity.ANTECEDENT;
        }
        if(ts.isSuccedent() && getNumNegations(ts, s, 0) % 2 == 1) {
            return TermSelector.SequentPolarity.ANTECEDENT;
        }
        return TermSelector.SequentPolarity.SUCCEDENT;
    }

    public static int getNumNegations(TermSelector ts, Sequent s, int idx) throws RuleException {
        if(idx <= ts.getSubtermSelector().getDepth()) {
            int[] array;
            try {
                array = ts.getPath().subList(0, idx).stream().mapToInt(i->i).toArray();
            } catch (IllegalArgumentException e) {
                array = new int[]{};
            }
            TermSelector currentTs;
            if(array.length != 0) {
                currentTs = new TermSelector(ts.getPolarity(), ts.getTermNo(), array);
            } else {
                currentTs = new TermSelector(ts.getPolarity(), ts.getTermNo());
            }
            Term t = currentTs.selectSubterm(s);
            if (t instanceof ApplTerm) {
                if (((ApplTerm) t).getFunctionSymbol() == BuiltinSymbols.NOT) {
                    return getNumNegations(ts, s, idx + 1) + 1;
                }
            }
        } else {
            return 0;
        }
        return getNumNegations(ts, s, idx + 1);
    }

    private String[] test(String ... s ) {
        return null;
    }
}
