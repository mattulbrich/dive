package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

public abstract class TopLevelFormula {

    private final ProofFormula formula;

    protected TopLevelFormula(ProofFormula formula) {
        this.formula = formula;
    }

    public Term getTerm() {
        return formula.getTerm();
    }

    public ProofFormula getProofFormula() { return formula; }

    public abstract <R> R accept(TopLevelFormulaVisitor<R> visitor);

}
