package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.term.Term;

public class OriginalFormula extends TopLevelFormula {

    protected final int indexInSequent;

    public OriginalFormula(int indexInSequent, Term term) {
        super(term);
        this.indexInSequent = indexInSequent;
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitOriginalFormula(this);
    }

    public int getIndexInSequent() {
        return indexInSequent;
    }
}
