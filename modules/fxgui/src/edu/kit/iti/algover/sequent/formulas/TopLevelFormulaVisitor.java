/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent.formulas;

public interface TopLevelFormulaVisitor<R> {

    R visitOriginalFormula(OriginalFormula formula);

    R visitDeletedFormula(DeletedFormula formula);

    R visitModifiedFormula(ModifiedFormula formula);

    R visitAddedFormula(AddedFormula formula);

}
