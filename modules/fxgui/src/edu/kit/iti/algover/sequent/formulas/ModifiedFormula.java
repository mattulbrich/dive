package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;

import java.util.Collection;

public class ModifiedFormula extends TopLevelFormula {

    private final Collection<SubtermSelector> modifiedParts;

    public ModifiedFormula(Collection<SubtermSelector> modifiedParts, Term term) {
        super(term);
        this.modifiedParts = modifiedParts;
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitModifiedFormula(this);
    }

    public Collection<SubtermSelector> getModifiedParts() {
        return modifiedParts;
    }
}
