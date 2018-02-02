/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

public abstract class SchemaTerm extends Term {

    public SchemaTerm(Sort sort, Term[] subterms) {
        super(sort, subterms);
    }

}
