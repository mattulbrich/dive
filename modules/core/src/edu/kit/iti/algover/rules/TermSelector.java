/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */

/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */

package edu.kit.iti.algover.rules;

import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.FormatException;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * The Class TermSelector is used to select a subterm from a sequent. It
 * description consists of 2 parts:
 * <ol>
 * <li>The side of the sequent, either ANTECEDENT or SUCCEDENT
 * <li>The number of the term on that side (starting at 0)
 * <li>The path to the subterm in that term (a {@link SubtermSelector})
 * </ol>
 *
 * <p>
 * The string representation of a TermSelector is of the form
 * <pre>
 * (A|S).number.number*
 * </pre>, for instance <code>A.1</code> for the whole second term on the
 * antecedent side and <code>S.2.0.1</code> for the the second subterm of the
 * first subterm of the third formula in the succedent.
 *
 * @see SubtermSelector
 *
 * @author mulbrich
 */
public final class TermSelector implements Comparable<TermSelector> {

    /**
     * We store the side of the sequent as a constant value.
     */
    private final @NonNull SequentPolarity polarity;

    /**
     * We use the Constant CLASS_EXC_INDICATOR to indicate the origin for error
     * messages. It holds the class name.
     */
    private static final String CLASS_EXC_INDICATOR = "TermSelector";

    /**
     * We create only one empty subterm selector to save space.
     */
    private static final SubtermSelector EMPTY_SUBTERMSELECTOR = new SubtermSelector();

    /**
     * Gets the polarity of this term selector.
     *
     * @return the constant for antecedent or succedent
     */
    public @NonNull SequentPolarity getPolarity() {
        return polarity;
    }

    /**
     * the number of the selected term on its side.
     */
    private final short termNumber;

    /**
     * If a subterm of the term is selected, then this field contains
     * the path to it.
     *
     * Note that an empty subterm selector can also refer to the top
     * level term as the 0th subterm.
     */
    private @NonNull SubtermSelector subtermSelector;


    /**
     * Instantiates a new toplevel term selector.
     *
     * @param inAntecedent
     *            the side of the sequent
     * @param termNo
     *            the toplevel term number
     */
    public TermSelector(SequentPolarity inAntecedent, int termNo) {

        // Checkstyle: IGNORE MultipleStringLiterals
        assert termNo >= 0 && termNo <= Short.MAX_VALUE :
            "TermSelectors need non-negative short values, but got " + termNo;

        this.polarity = inAntecedent;
        this.termNumber = (short) termNo;
        this.subtermSelector = EMPTY_SUBTERMSELECTOR;
    }

    /**
     * Instantiates a new term selector from path informations.
     *
     * @param inAntecedent
     *            the side of the sequent
     * @param termNo
     *            the toplevel term number
     * @param path
     *            the path to the subterm in the given term
     */
    public TermSelector(SequentPolarity inAntecedent, int termNo, int... path) {

        assert termNo >= 0 && termNo <= Short.MAX_VALUE :
            "TermSelectors need non-negative short values, but got " + termNo;

        this.polarity = inAntecedent;
        this.termNumber = (short) termNo;

        // null check is needed, because "new TermSelector(true, 0, null);" is a
        // valid java expression
        if(path != null && path.length > 0) {
            this.subtermSelector = new SubtermSelector(path);
        } else {
            this.subtermSelector = EMPTY_SUBTERMSELECTOR;
        }
    }

    /**
     * Instantiates a new term selector from a term selector and a subterm
     * number.
     *
     * <p>
     * The created selector contains the same information as the argument.
     * Only the path to the subterm is augmented by the given path.
     *
     * @param termSelector
     *            the term selector to modify
     * @param path
     *            the path to select
     */
    public TermSelector(TermSelector termSelector, int... path) {

        this.polarity = termSelector.polarity;
        this.termNumber = termSelector.termNumber;
        this.subtermSelector = new SubtermSelector(termSelector.subtermSelector, path);
    }

    /**
     * Instantiates a new term selector from a term selector and a subterm
     * number.
     *
     * <p>
     * The created selector contains the same information as the argument.
     * Only the path to the subterm is augmented by the given path.
     *
     * @param termSelector
     *            the term selector to modify
     * @param subSelector
     *            the path to select
     */
    public TermSelector(TermSelector termSelector, SubtermSelector subSelector) {
        this.polarity = termSelector.polarity;
        this.termNumber = termSelector.termNumber;
        this.subtermSelector = new SubtermSelector(termSelector.subtermSelector, subSelector);
    }

    /**
     * Instantiates a new term selector from a string description.
     *
     * The first character needs to be either 'A' or 'S' followed by a dot followed
     * by a non-negative number followed by a dot and another non-negative
     * number, etc. As production this is:
     * <pre>
     * TermSelector ::= ( 'A' | 'S' ) ( '.' NonNegNumber )+
     * </pre>
     * <p>The result of {@link #toString()} can be parsed in again.
     *
     * @param descr
     *            a string description of a TermSelector
     *
     * @throws FormatException
     *             if the string is incorrectly formatted
     */
    public TermSelector(String descr) throws FormatException {

        if (descr.startsWith(".") || descr.endsWith(".")) {
            throw new FormatException(CLASS_EXC_INDICATOR,
                    "Illegal character at start/end: .", descr);
        }

        String[] sect = descr.split("\\.", 3);

        if (sect.length < 2) {
            throw new FormatException(CLASS_EXC_INDICATOR,
                    "Term selector needs at least 2 parts:", descr);
        }

        if ("A".equals(sect[0])) {
            polarity = SequentPolarity.ANTECEDENT;
        } else if ("S".equals(sect[0])) {
            polarity = SequentPolarity.SUCCEDENT;
        } else {
            throw new FormatException(CLASS_EXC_INDICATOR, "unknown first part: " + sect[0], descr);
        }

        if (sect[1].length() == 0) {
            throw new FormatException(CLASS_EXC_INDICATOR, "empty term number", descr);
        }

        try {
            termNumber = Byte.parseByte(sect[1]);
            if (termNumber < 0) {
                throw new FormatException(CLASS_EXC_INDICATOR, "negative: "
                        + sect[1], descr);
            }
        } catch (NumberFormatException e) {
            throw new FormatException(CLASS_EXC_INDICATOR, "not a number: "
                    + sect[1], descr);
        }

        if (sect.length == 3) {
            subtermSelector = new SubtermSelector(sect[2]);
        } else {
            subtermSelector = EMPTY_SUBTERMSELECTOR;
        }

    }

    /**
     * a string representation of the TermSelector. We create an equal object if
     * parsing this string using {@link TermSelector#TermSelector(String)}.
     *
     * @return a string representation of this object
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(isAntecedent() ? "A." : "S.");
        sb.append(termNumber);
        String st = subtermSelector.toString();
        if(st.length() > 0) {
            sb.append(".").append(st);
        }
        return sb.toString();
    }

    /**
     * Gets the depth of this selector.
     * The depth is the number of sub term selections needed to find the desired term.
     * It is the length of the path plus one (for selecting the top level term)
     *
     * @return a number >= 0
     */
    public int getDepth() {
        return subtermSelector.getDepth();
    }

    /**
     * An object is equal to this if it is a TermSelector and all three
     * indicators have the same value.
     *
     * @param obj
     *            object to compare to
     * @return true iff obj refers to the same term as this
     */
    @Override
    public boolean equals(@Nullable Object obj) {
        if (obj instanceof TermSelector) {
            TermSelector ts = (TermSelector) obj;
            if(isAntecedent() != ts.isAntecedent()) {
                return false;
            }

            if(getDepth() != ts.getDepth()) {
                return false;
            }

            if(termNumber != ts.termNumber) {
                return false;
            }

            return subtermSelector.equals(ts.subtermSelector);
        }
        return false;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * The result for this implementation is the comparison of the string
     * representations. That is, it is the same as if calling
     * {@code toString().compareTo(ts.toString())}.
     */
    @Override
    public int compareTo(TermSelector ts) {
        if(polarity != ts.polarity) {
            // return -1 if I am antecedent and ts is succedent
            return isAntecedent() ? -1 : 1;
        }

        // different term number
        if(termNumber != ts.termNumber) {
            return termNumber - ts.termNumber;
        }

        // delegate to subtermselector
        return subtermSelector.compareTo(ts.subtermSelector);
    }

    /**
     * {@inheritDoc}
     *
     * <p>The hash code is calculated from the path.
     */
    @Override public int hashCode() {

        int h = isAntecedent() ? -1 : 1;
        h *= termNumber;
        h ^= subtermSelector.hashCode();
        return h;
    }

    /**
     * check whether the selection refers to the antecedent side of a sequent.
     *
     * @return true, if the selection is on the antecedent soide
     */
    public boolean isAntecedent() {
        return polarity == SequentPolarity.ANTECEDENT;
    }

    /**
     * check whether the selection refers to the succedent side of a sequent.
     *
     * @return true, if the selection is on the succedent side
     */
    public boolean isSuccedent() {
        return polarity == SequentPolarity.SUCCEDENT;
    }

    /**
     * Create a sequent object from the selected toplevel formula.
     *
     * @param sequent
     *            the sequent to choose from
     * @return the sequent containing only the selected toplevel formula.
     * @throws RuleException
     *             if the selection cannot be applied to the sequent.
     */
    public Sequent selectAsSequent(@NonNull Sequent sequent) throws RuleException {
        ProofFormula formula = selectTopterm(sequent);
        if (isAntecedent()) {
            return new Sequent(Collections.singletonList(formula), Collections.emptyList());
        } else {
            return new Sequent(Collections.emptyList(), Collections.singletonList(formula));
        }
    }

    /**
     * Checks if this selection refers to a top level term.
     *
     * @return true, if the subterm number is equal to 0
     */
    public boolean isToplevel() {
        return getDepth() == 0;
    }

    /**
     * Gets the toplevel selector to which this selector is a subselection.
     *
     * @return a term selector which is "prefix" to this.
     */
    public@NonNull TermSelector getToplevelSelector() {
        return new TermSelector(polarity, termNumber);
    }

    /**
     * If this selector selects a top level term, then this method selects a
     * subterm of the term.
     *
     * @param subtermNo
     *            the subterm number of the term to select
     *
     * @return a TermSelector with side and term number as this object and the
     *         subterm subtermNo
     */
    public TermSelector selectSubterm(int subtermNo) {
        return new TermSelector(this, subtermNo);
    }

    /**
     * Gets the number of the toplevel term to which the
     * selection refers to.
     *
     * @return the number of the term (starting at 0)
     */
    public int getTermNo() {
        return termNumber;
    }

    /**
     * Gets the path as list of integers.
     *
     * @return the path to the selected subterm as unmodifiable list.
     */
    public @NonNull List<Integer> getPath() {
        return subtermSelector.getPath();
    }

    /**
     * Apply the term selector to a sequent to select a particular top level
     * term. This method ignores the path selection information.
     *
     * <p>
     * The selection can fail, if the index is out of range.
     *
     * @param sequent
     *            the sequent to select from
     *
     * @return the term to which the selector refers
     *
     * @throws RuleException
     *             if the selection cannot be applied to the sequent.
     */
    public @NonNull
    ProofFormula selectTopterm(@NonNull Sequent sequent) throws RuleException {
        List<ProofFormula> terms;
        if (isAntecedent()) {
            terms = sequent.getAntecedent();
        } else {
            terms = sequent.getSuccedent();
        }

        int termNo = getTermNo();
        if (termNo < 0 || termNo >= terms.size()) {
            throw new RuleException("Cannot select " + this + " in " + sequent);
        }

        return terms.get(termNo);
    }

    /**
     * Apply the term selector to a sequent to select a particular term.
     *
     * <p>
     * This method takes the term selection and the path selection information
     * into consideration.
     *
     * <p>
     * The selection can fail, if an index (either term index or a subterm index)
     * are out of range.
     *
     * @param sequent
     *            the sequent to select from
     *
     * @return the term to which the selector refers
     *
     * @throws RuleException
     *             if the selection cannot be applied to the sequent.
     */
    public @NonNull
    Term selectSubterm(@NonNull Sequent sequent) throws RuleException {
        ProofFormula formula = selectTopterm(sequent);
        return subtermSelector.selectSubterm(formula.getTerm());
    }

    /**
     * Checks whether this term selector has another term selector as prefix.
     *
     * <p>
     * The result is equivalent to
     * <pre>this.toString().startsWith(prefix.toString())</pre>
     *
     * @param prefix
     *            the term selector which may be a prefix to this.
     *
     * @return true iff the argument is a prefix to this selector.
     */
    public boolean hasPrefix(@NonNull TermSelector prefix) {
        if (polarity != prefix.polarity) {
            return false;
        }

        if(getTermNo() != prefix.getTermNo()) {
            return false;
        }

        return getSubtermSelector().hasPrefix(prefix.getSubtermSelector());
    }

    /**
     * Returns a bool stating whether or not this TermSelector is valid for the given sequent (meaning it points to
     * a Term)
     * @param s The sequent the TermSelector should be checked for
     * @return whether or not this selector is valid for the given sequent
     */
    public boolean isValidForSequent(Sequent s) {
        try {
            this.selectSubterm(s);
            return true;
        } catch (RuleException e) {
            return false;
        }
    }

    public SubtermSelector getSubtermSelector() {
        return subtermSelector;
    }


    /**
     * Indicator to denote left and right hand side of the sequent.
     */
    public enum SequentPolarity {
        ANTECEDENT, SUCCEDENT;

        /**
         * Gets the opposite polarity.
         *
         * @return an non-<code>null</code> object of this class different from
         * <code>this</code>
         */
        public SequentPolarity getOpposite() {
            return this == ANTECEDENT ? SUCCEDENT : ANTECEDENT;
        }
    }
}
