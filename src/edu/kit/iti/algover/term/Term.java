package edu.kit.iti.algover.term;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.util.Util;

public abstract class Term {

    public static final Term[] NO_TERMS = new Term[0];

    private final Sort sort;
    private final Term[] subterms;

    /**
     *
     * @param sort
     * @param subterms
     *
     */
    public Term(Sort sort, Term[] subterms) {
        this.sort = sort;
        this.subterms = subterms;
    }

    public Sort getSort() {
        return sort;
    }

    public List<Term> getSubterms() {
        return Util.readOnlyArrayList(subterms);
    }

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

    public abstract <A,R> R accept(TermVisitor<A, R> visitor, A arg);
}
