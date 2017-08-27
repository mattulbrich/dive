package edu.kit.iti.algover.refrenceTypes;

/**
 * Created by Philipp on 27.08.2017.
 */
public interface ReferenceVisitor<R> {

    R visit(CodeReference codeTarget);

    R visit(ProofTermReference termTarget);

    R visit(UserInputReference userInputTarget);
}
