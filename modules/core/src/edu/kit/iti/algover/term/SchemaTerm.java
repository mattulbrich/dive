/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import nonnull.NonNull;

/**
 * Schema terms are terms that can be used in matching expressions and can be
 * used by rules. They are not to occur on the level of concrete sequent
 * terms.
 *
 * @author Mattias Ulbrich
 */
public abstract class SchemaTerm extends Term {

    public SchemaTerm(Sort sort, Term[] subterms) {
        super(sort, subterms);
    }

    /**
     * Get a term which coincides with this term but with a more concrete type.
     *
     * Schematic terms may have placeholder terms that need to be refined later.
     *
     * @param newSort the sort to refine to.
     * @return a term similar to this of sort <code>newSort</code>
     */
    public abstract SchemaTerm refineSort(@NonNull Sort newSort);

}
