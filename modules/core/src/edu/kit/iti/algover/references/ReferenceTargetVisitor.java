package edu.kit.iti.algover.references;

/**
 * Created by Philipp on 27.08.2017.
 */
public interface ReferenceTargetVisitor<R> {

    R visit(CodeReferenceTarget codeTarget);

    R visit(ProofTermReferenceTarget termTarget);

    R visit(UserInputReferenceTarget userInputTarget);

    R visit(ScriptReferenceTarget scriptTarget);

}
