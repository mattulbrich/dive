package edu.kit.iti.algover.term;

public class QuantTerm extends Term {

    enum Quantifier {
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

}
