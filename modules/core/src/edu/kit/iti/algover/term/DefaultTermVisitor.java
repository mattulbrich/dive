package edu.kit.iti.algover.term;

public abstract class DefaultTermVisitor<A, R> implements TermVisitor<A, R> {

    protected abstract R defaultVisit(Term term, A arg);

    @Override
    public R visit(ApplTerm term, A arg) {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(VariableTerm term, A arg) {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(SchemaVarTerm term, A arg) {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(QuantTerm term, A arg) {
        return defaultVisit(term, arg);
    }

    @Override
    public R visit(LetTerm term, A arg) {
        return defaultVisit(term, arg);
    }
}
