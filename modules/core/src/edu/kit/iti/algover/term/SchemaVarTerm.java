/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

public class SchemaVarTerm extends Term {

    private static final Sort UNTYPED_SORT = new Sort("<UNTYPED>");

    private final String name;

    public SchemaVarTerm(String name, Sort sort) {
        super(sort, Term.NO_TERMS);
        this.name = name;
    }

    public SchemaVarTerm(String name) {
        this(name, UNTYPED_SORT);
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public <A, R, E extends Exception>
            R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

    @Override
    public boolean hasSort(Sort sort) {
        return super.hasSort(sort) || this.getSort() == UNTYPED_SORT;
    }

    public String getName() {
        return name;
    }

}
