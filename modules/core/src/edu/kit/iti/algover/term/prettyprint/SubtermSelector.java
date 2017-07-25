/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
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


package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.Term;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.AbstractList;
import java.util.Arrays;
import java.util.List;

/**
 * The Class TermSelector is used to select a subterm within a term.
 *
 * <p>
 * It does not necessarily describe a direct subterm but may describe a term at
 * arbitrary depth. It is represented by a possibly empty list of indices of
 * subterms.
 *
 * <p>
 * The string representation of a TermSelector is a list of non-negative
 * integers separated by colons for instance <code>0.1</code> for the the
 * second subterm of the first subterm of the term to which it is applied or the
 * empty selector for the formula itself
 *
 * <p>
 * We silently assume that no term has more than 127 subterms. This is also
 * checked by assertions.
 *
 * @see TermSelector
 */
public final class SubtermSelector implements Comparable<SubtermSelector> {

    /**
     * The Constant CLASS_EXC_INDICATOR is used in exception messages to
     * indicate the origin.
     */
    private static final String CLASS_EXC_INDICATOR = "SubtermSelector";

    /**
     * The path of subterm numbers.
     */
    private byte[] selectorInfo;

    /**
     * Helper class granting access the path as an unmodifiable list.
     */
    private class ListView extends AbstractList<Integer> {
        @Override public Integer get(int index) {
            return (int)selectorInfo[index];
        }
        @Override public int size() {
            return selectorInfo.length;
        }
    }

    /**
     * Instantiates a new term selector from path informations.
     *
     * @param path
     *            the path to the subterm in the given term
     */
    public SubtermSelector(int... path) {
        this.selectorInfo = new byte[path.length];

        for (int i = 0; i < path.length; i++) {
            assert path[i] >= 0 && path[i] <= Byte.MAX_VALUE :
                "SubtermSelectors must be non-negative byte values, but got: " + path[i];
            this.selectorInfo[i] = (byte) path[i];
        }
    }

    /**
     * Instantiates a new term selector from a subterm selector and an
     * additional path.
     *
     * <p>
     * The created selector is the first argument's path augmented by the second
     * argument.
     *
     * @param termSelector
     *            the term selector to modify
     * @param path
     *            the path to augment
     */
    public SubtermSelector(@NonNull SubtermSelector termSelector, int... path) {
        int orgLen = termSelector.getDepth();

        selectorInfo = new byte[orgLen + path.length];

        System.arraycopy(termSelector.selectorInfo, 0,
                selectorInfo, 0, orgLen);

        for (int i = 0; i < path.length; i++) {
            assert path[i] >= 0 && path[i] <= Byte.MAX_VALUE;
            selectorInfo[i + orgLen] = (byte) path[i];
        }
    }

    /**
     * Instantiates a new sub term selector from two sub term selectors by
     * concatenating them.
     *
     * <p>
     * The created selector the first argument's path augmented by the second
     * argument.
     *
     * @param sel1
     *            the first selector
     * @param sel2
     *            the second selector
     */
    public SubtermSelector(@NonNull SubtermSelector sel1,
            @NonNull SubtermSelector sel2) {

        int len1 = sel1.getDepth();
        int len2 = sel2.getDepth();
        selectorInfo = new byte[len1 + len2];

        System.arraycopy(sel1.selectorInfo, 0, selectorInfo, 0, len1);
        System.arraycopy(sel2.selectorInfo, 0, selectorInfo, len1, len2);
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
    // TODO ADAPT EXCPETION
    public SubtermSelector(@NonNull String descr) throws FormatException {

        if(descr.startsWith(".") || descr.endsWith(".")) {
            throw new FormatException("TermSelector", "Illegal character at start/end: .", descr);
        }

        if(descr.length() == 0) {
            // empty selector describes the toplevel term itself
            selectorInfo = new byte[0];
            return;
        }

        String[] sect = descr.split("\\.");
        selectorInfo = new byte[sect.length];

        for (int i = 0; i < selectorInfo.length; i++) {
            try {
                if(sect[i].length() == 0) {
                    throw new FormatException(CLASS_EXC_INDICATOR, "empty part", descr);
                }
                selectorInfo[i] = Byte.parseByte(sect[i]);
                if (selectorInfo[i] < 0) {
                    throw new FormatException(CLASS_EXC_INDICATOR, "negative: "
                            + sect[i], descr);
                }
            } catch (NumberFormatException e) {
                throw new FormatException(CLASS_EXC_INDICATOR, "not a number: "
                        + sect[i], descr);
            }
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
        for (int i = 0; i < selectorInfo.length; i++) {
            if(i > 0) {
                sb.append(".");
            }
            sb.append(selectorInfo[i]);
        }
        return sb.toString();
    }

    /**
     * Gets the depth of this selector. The depth is the number of sub term
     * selections needed to find the desired term. It is the length of the path,
     * 0 if the top level term itself is selected.
     *
     * @return a number >= 0
     */
    public int getDepth() {
        return selectorInfo.length;
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
        if (obj instanceof SubtermSelector) {
            SubtermSelector ts = (SubtermSelector) obj;
            if(getDepth() != ts.getDepth()) {
                return false;
            }

            for (int i = 0; i < selectorInfo.length; i++) {
                if(selectorInfo[i] != ts.selectorInfo[i]) {
                    return false;
                }
            }

            return true;
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
    public int compareTo(SubtermSelector sts) {
        int len = selectorInfo.length;
        int len2 = sts.selectorInfo.length;
        for (int i = 0; i < len; i++) {
            if(i >= len2) {
                // sts is prefix of this
                return 1;
            }

            if(selectorInfo[i] != sts.selectorInfo[i]) {
                return selectorInfo[i] - sts.selectorInfo[i];
            }
        }

        // equal if same length, otherwise this is prefix to sts
        return len == len2 ? 0 : -1;
    }

    /**
     * {@inheritDoc}
     *
     * <p>The hash code is calculated from the path.
     */
    @Override public int hashCode() {
        return Arrays.hashCode(selectorInfo);
    }

    //        /**
    //         * If this selector selects a top level term, then this method selects a
    //         * subterm of the term.
    //         *
    //         * @param subtermNo
    //         *            the subterm number of the term to select
    //         *
    //         * @return a TermSelector with side and term number as this object and the
    //         *         subterm subtermNo
    //         *
    //         * @deprecated Use {@link #SubtermSelector(SubtermSelector, int)} instead
    //         */
    //        @Deprecated
    //        public SubtermSelector selectSubterm(int subtermNo) {
    //            return new SubtermSelector(this, subtermNo);
    //        }

    /**
     * Gets the path as list of integers.
     *
     * @return the path to the selected subterm as unmodifiable list.
     */
    public List<Integer> getPath() {
        return new ListView();
    }


    /**
     * Gets the linear index of a subterm.
     *
     * If enumerating all subterms in an infix tree visiting fashion, this index
     * would result in the selected term. SubtermCollector provides such a
     * linear list for instance.
     *
     * @param term
     *            the term to select in
     *
     * @return the linear index
     * @see SubtermCollector
     */
    public int getLinearIndex(@NonNull Term term) {
        int result = 0;

        for (int i = 0; i < selectorInfo.length; i++) {
            int v = selectorInfo[i];
            for(int j = 0; j < v; j++) {
                result += countAllSubterms(term.getTerm(j));
            }
            result ++;
            term = term.getTerm(v);
        }
        return result;
    }

    /* needed fot getLinearIndex */
    private int countAllSubterms(Term term) {
        // count myself as well
        int result = 1;
        for (int i = 0; i < term.countTerms(); i++) {
            result += countAllSubterms(term.getTerm(i));
        }

        return result;
    }


    /**
     * Apply the term selector to a term to select a particular subterm.
     *
     * <p>
     * The selection can fail, if an index (either term index or a subterm
     * index) is out of range.
     *
     * @param term
     *            the term to select from
     *
     * @return the subterm of <code>term</code> specified by this selector
     *
     * @throws ProofException
     *             if the selection cannot be applied to the term.
     */
    public Term selectSubterm(@NonNull Term term) throws Exception {

        for (int i = 0; i < selectorInfo.length; i++) {
            byte subtermNo = selectorInfo[i];
            if(subtermNo >= term.countTerms()) {
                throw new Exception("Cannot select " + subtermNo + " in "
                        + term + " for " + this);
            }

            term = term.getTerm(subtermNo);
        }

        return term;
    }

    /**
     * Gets the subterm number which is stored in position <code>index</code>
     * in the path of this object.
     *
     * @param index
     *            an index between 0 (incl) and {@link #getDepth()} (excl)
     *
     * @return the subterm number in path at the given index
     * @throws IndexOutOfBoundsException
     *             if the the given index is outside the specified bounds
     */
    public int getSubtermNumber(int index) {
        return selectorInfo[index];
    }

    /**
     * Checks whether this object has the argument as prefix.
     *
     * For instance: [0,1] is a prefix of [0,1,0] and of [0,1] but not of [1,1]
     * or [0].
     *
     * @param stSel
     *            another subtermselector.
     *
     * @return true, if the argument is a prefix for this selector.
     */
    public boolean hasPrefix(@NonNull SubtermSelector stSel) {
        if(getDepth() < stSel.getDepth()) {
            return false;
        }

        for (int i = 0; i < stSel.getDepth(); i++) {
            if(selectorInfo[i] != stSel.selectorInfo[i]) {
                return false;
            }
        }

        return true;
    }
}
