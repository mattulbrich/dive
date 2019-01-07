package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.term.Term;

public class AddedOrDeletedFormula extends TopLevelFormula {

    public enum Type {
        ADDED, DELETED;
    }

    private final Type type;

    public AddedOrDeletedFormula(Type type, Term term) {
        super(term);
        this.type = type;
    }

    @Override
    public <R> R accept(TopLevelFormulaVisitor<R> visitor) {
        return visitor.visitAddedOrDeletedFormula(this);
    }

    public Type getType() {
        return type;
    }
}
