/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.term;

public class SchemaOccurTerm extends SchemaTerm {

    public SchemaOccurTerm(Term occurTerm) {
        super(Sort.UNTYPED_SORT, new Term[] { occurTerm });
    }

    @Override
    public String toString() {
        return "(... " + getTerm(0) + " ...)";
    }

    @Override
    public <A, R, E extends Exception> R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

}
