/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

public abstract class SchemaTerm extends Term {

    public SchemaTerm(Sort sort, Term[] subterms) {
        super(sort, subterms);
    }

    public abstract SchemaTerm refineSort(Sort newSort);

}
