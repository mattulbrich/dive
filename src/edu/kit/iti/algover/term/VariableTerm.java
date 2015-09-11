package edu.kit.iti.algover.term;

public class VariableTerm extends Term {

    private final String name;

    public VariableTerm(String name, Sort sort) {
        super(sort, Term.NO_TERMS);
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

}
