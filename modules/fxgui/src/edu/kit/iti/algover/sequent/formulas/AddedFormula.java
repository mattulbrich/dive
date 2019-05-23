package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.proof.ProofFormula;

/**
 * Created by jklamroth on 1/9/19.
 */
public class AddedFormula extends OriginalFormula {
    public AddedFormula(int indexInSequent, ProofFormula term) {
        super(indexInSequent, term);
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitAddedFormula(this);
    }
}
