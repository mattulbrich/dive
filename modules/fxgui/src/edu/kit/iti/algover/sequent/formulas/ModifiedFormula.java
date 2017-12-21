package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;

public class ModifiedFormula extends TopLevelFormula {

    private final SubtermSelector modifiedPart;

    public ModifiedFormula(SubtermSelector modifiedPart, Term term) {
        super(term);
        this.modifiedPart = modifiedPart;
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitModifiedFormula(this);
    }

    public SubtermSelector getModifiedPart() {
        return modifiedPart;
    }
}
