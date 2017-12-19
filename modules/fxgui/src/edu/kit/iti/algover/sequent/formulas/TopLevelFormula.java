package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.term.Term;

public abstract class TopLevelFormula {

    private final Term term;

    protected TopLevelFormula(Term term) {
        this.term = term;
    }

    public Term getTerm() {
        return term;
    }

    public abstract <R> R accept(TopLevelFormulaVisitor<R> visitor);

}
