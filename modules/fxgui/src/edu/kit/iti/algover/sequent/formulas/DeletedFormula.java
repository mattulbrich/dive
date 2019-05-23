/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.term.Term;

public class DeletedFormula extends TopLevelFormula {

    public DeletedFormula(Term term) {
        super(term);
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitDeletedFormula(this);
    }
}
