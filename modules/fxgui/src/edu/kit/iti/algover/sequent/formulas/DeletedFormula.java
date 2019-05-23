package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

public class DeletedFormula extends TopLevelFormula {

    public DeletedFormula(ProofFormula term) {
        super(term);
    }

    public DeletedFormula(Term term) {
        this(new ProofFormula(term));
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitDeletedFormula(this);
    }
}
