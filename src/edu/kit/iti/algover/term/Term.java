/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.List;

import edu.kit.iti.algover.util.Util;

/**
 * The superclass for all terms/formulas.
 *
 * It only features subterms. More functionality is provided only in the
 * subclases.
 *
 * Terms are immutable objects.
 *
 * TODO add anchors and/or labels to this class
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
        this.sort = sort;
        this.subterms = subterms;
    }

    /**
     * Gets the sort of this term.
     *
     * @return the non-<code>null</code> sort
     */
    public Sort getSort() {
        return sort;
    }

    /**
     * Gets the subterms for this term.
     *
     * @return an unmodifiable view on the subterms
     */
    public List<Term> getSubterms() {
        return Util.readOnlyArrayList(subterms);
    }

    /**
     * Gets the term.
     *
     * @param i the i
     * @return the term
     */
    public Term getTerm(int i) {
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
        if(getClass() != obj.getClass()) {
            return false;
        }

        Term other = (Term) obj;
        return sort.equals(other.sort) &&
                Arrays.equals(subterms, other.subterms);
    }

    /**
     * Accept.
     *
     * @param <A> the generic type
     * @param <R> the generic type
     * @param visitor the visitor
     * @param arg the arg
     * @return the r
     */
    public abstract <A,R> R accept(TermVisitor<A, R> visitor, A arg);

    /**
     * Count terms.
     *
     * @return the int
     */
    public int countTerms() {
        return subterms.length;
    }
}
