package edu.kit.iti.algover.sequent.formulas;

public interface TopLevelFormulaVisitor<R> {

    R visitOriginalFormula(OriginalFormula formula);

    R visitAddedOrDeletedFormula(AddedOrDeletedFormula formula);

    R visitModifiedFormula(ModifiedFormula formula);

}
