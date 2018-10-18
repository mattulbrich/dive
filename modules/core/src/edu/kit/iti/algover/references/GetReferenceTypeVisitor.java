package edu.kit.iti.algover.references;

import java.util.HashMap;

public class GetReferenceTypeVisitor<T extends Reference> implements ReferenceVisitor<T> {

    private final Class<T> clazz;

    public GetReferenceTypeVisitor(Class<T> clazz) {
        this.clazz = clazz;
    }

    @Override
    public T visit(CodeReference codeTarget) {
        return clazz.isInstance(codeTarget) ? clazz.cast(codeTarget) : null;
    }

    @Override
    public T visit(ProofTermReference termTarget) {
        return clazz.isInstance(termTarget) ? clazz.cast(termTarget) : null;
    }

    @Override
    public T visit(UserInputReference userInputTarget) {
        return clazz.isInstance(userInputTarget) ? clazz.cast(userInputTarget) : null;
    }
}
