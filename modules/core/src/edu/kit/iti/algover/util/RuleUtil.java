package edu.kit.iti.algover.util;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

import java.util.List;
import java.util.Optional;
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

}
