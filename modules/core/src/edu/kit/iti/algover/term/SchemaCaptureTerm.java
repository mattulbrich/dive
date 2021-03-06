/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;

public class SchemaCaptureTerm extends SchemaTerm {

    private final String name;

    public SchemaCaptureTerm(String name, Term innerTerm) {
        super(innerTerm.getSort(), new Term[] { innerTerm });
        assert name.startsWith("?") : "Names of capture schema variables must begin with a '?'";
        this.name = name;
    }

    @Override
    public String toString() {
        return "(" + name + ": " + getTerm(0) + ")";
    }

    @Override
    public <A, R, E extends Exception> R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

    @Override
    public SchemaTerm refineSort(Sort newSort) {
        assert false : "This cannot be refined";
        return this;
    }

    public String getName() {
        return name;
    }
}
