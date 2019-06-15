/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

public class SchemaOccurTerm extends SchemaTerm {

    public SchemaOccurTerm(Term occurTerm, Sort sort) {
        super(sort, new Term[] { occurTerm });
    }

    public SchemaOccurTerm(Term occurTerm) {
        this(occurTerm, Sort.UNTYPED_SORT);
    }

    @Override
    public String toString() {
        return "(... " + getTerm(0) + " ...)";
    }

    @Override
    public <A, R, E extends Exception> R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

    @Override
    public SchemaTerm refineSort(Sort newSort) {
        assert getSort().equals(Sort.UNTYPED_SORT);
        return new SchemaOccurTerm(getTerm(0), newSort);
    }
}
