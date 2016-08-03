package edu.kit.iti.algover.term;

public class SchemaVarTerm extends Term {

    private final String name;

    public SchemaVarTerm(String name, Sort sort) {
        super(sort, Term.NO_TERMS);
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public <A, R> R accept(TermVisitor<A, R> visitor, A arg) {
        return visitor.visit(this, arg);
    }

}
