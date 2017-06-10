/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

public abstract class DefaultTermVisitor<A, R, E extends Exception>
                implements TermVisitor<A, R, E> {

    protected abstract R defaultVisit(Term term, A arg);

    @Override
    public R visit(ApplTerm term, A arg) throws E {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(VariableTerm term, A arg) throws E {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(SchemaVarTerm term, A arg) throws E {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(QuantTerm term, A arg) throws E {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(LetTerm term, A arg) throws E {
        return defaultVisit(term, arg);
    }
}
