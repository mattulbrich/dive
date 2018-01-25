package edu.kit.iti.algover.script.interpreter;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.Signature;
import edu.kit.iti.algover.script.data.VariableAssignment;

import java.util.List;

/**
 * Matcher for Terms
 */
public class TermMatcher<T> implements MatcherApi<T> {
    @Override
    public List<VariableAssignment> matchLabel(ProofNode currentState, String label) {
        return null;
    }

    @Override
    public List<VariableAssignment> matchSeq(ProofNode currentState, String data, Signature sig) {
        return null;
    }
}
