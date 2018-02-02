/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import edu.kit.iti.algover.util.Util;

/**
 * The superclass for all terms/formulas.
 *
 * It only features subterms. More functionality is provided only in the
 * subclases.
 *
 * Terms are immutable objects.
 *
 * @author Mattias Ulbrich
 */
public abstract class Term {

    /**
     * The array NO_TERMS can be used to generate terms w/o subterms.
     */
    public static final Term[] NO_TERMS = new Term[0];

    /**
     * The sort of this term.
     */
    private final Sort sort;

    /**
     * The subterms of this term.
     */
    private final Term[] subterms;

    /**
     * Instantiates a new term with given subterms.
     *
     * @param sort the non-<code>null</code> sort
     * @param subterms the deep non-<code>null</code> subterms
     */
    public Term(Sort sort, Term[] subterms) {
        this.sort = Objects.requireNonNull(sort);
        this.subterms = Util.requireDeepNonNull(subterms);
    }

    /**
     * Gets the sort of this term.
     *
     * @return the non-<code>null</code> sort
     */
    public final Sort getSort() {
        return sort;
    }

    /**
     * Gets the subterms for this term.
     *
     * @return an unmodifiable view on the subterms
     */
    public final List<Term> getSubterms() {
        return Util.readOnlyArrayList(subterms);
    }

    /**
     * Access a subterm of this term.
     *
     * @param i
     *            the number (0 is the first) of the subterms to retrieve.
     * @return the non-<code>null</code> i-th suberm of this term
     * @throws IndexOutOfBoundsException
     *             if i is negative or not less than {@link #countTerms()}
     */
    public final Term getTerm(int i) {
        return subterms[i];
    }

    @Override
    public abstract String toString();

    @Override
    public int hashCode() {
        return Arrays.hashCode(subterms) ^ sort.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }

        Term other = (Term) obj;
        return sort.equals(other.sort)
            && Arrays.equals(subterms, other.subterms);
    }

    /**
     * Accept a {@link TermVisitor}.
     *
     * This is part of a visitor pattern.
     *
     * @param <A>
     *            the generic type for arguments
     * @param <R>
     *            the generic type for results
     * @param <E>
     *            the exception the visitation is allowed to throw.
     * @param visitor
     *            the visitor to work on this
     * @param arg
     *            the generic argument
     * @return the result of the visitor.
     * @throws E
     *             whenever the visitation fails. (Implementation-dependent)
     */
    public abstract <A, R, E extends Exception>
         R accept(TermVisitor<A, R, E> visitor, A arg) throws E;

    /**
     * Count the subterms of this instance.
     *
     * @return the non-negative number of subterms to this.
     */
    public final int countTerms() {
        return subterms.length;
    }
}
