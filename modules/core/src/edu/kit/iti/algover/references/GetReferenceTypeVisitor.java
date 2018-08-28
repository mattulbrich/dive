package edu.kit.iti.algover.references;

public class GetReferenceTypeVisitor<T extends ReferenceTarget> implements ReferenceTargetVisitor<T> {

    private final Class<T> clazz;

    public GetReferenceTypeVisitor(Class<T> clazz) {
        this.clazz = clazz;
    }

    @Override
    public T visit(CodeReferenceTarget codeTarget) {
        return clazz.isInstance(codeTarget) ? (T) codeTarget : null;
    }

    @Override
    public T visit(ProofTermReferenceTarget termTarget) {
        return clazz.isInstance(termTarget) ? (T) termTarget : null;
    }

    @Override
    public T visit(UserInputReferenceTarget userInputTarget) {
        return clazz.isInstance(userInputTarget) ? (T) userInputTarget : null;
    }

    @Override
    public T visit(ScriptReferenceTarget scriptTarget) {
        return clazz.isInstance(scriptTarget)? (T) scriptTarget: null ;
    }
}
