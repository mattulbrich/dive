package edu.kit.iti.algover.term;

public class QuantTerm extends Term {

    public enum Quantifier {
        FORALL, EXISTS
    };

    private final VariableTerm boundVar;
    private final Quantifier quantifier;

    public QuantTerm(Quantifier quantifier, VariableTerm boundVar, Term term) {
        super(Sort.FORMULA, new Term[] { term });
        this.boundVar = boundVar;
        this.quantifier = quantifier;
    }

    @Override
    public String toString() {
        return "(" + quantifier + " " + boundVar + ":" + boundVar.getSort()
                + " :: " + getTerm(0) + ")";
    }

    @Override
    public <A, R> R accept(TermVisitor<A, R> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public VariableTerm getBoundVar() {
        return boundVar;
    }

    public Quantifier getQuantifier() {
        return quantifier;
    }

}
