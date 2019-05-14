package edu.kit.iti.algover.sequent.formulas;

public interface TopLevelFormulaVisitor<R> {

    R visitOriginalFormula(OriginalFormula formula);

    R visitDeletedFormula(DeletedFormula formula);

    R visitModifiedFormula(ModifiedFormula formula);

    R visitAddedFormula(AddedFormula formula);

}
