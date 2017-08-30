package edu.kit.iti.algover.script.interpreter;

import edu.kit.iti.algover.script.ast.Signature;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.VariableAssignment;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.17)
 */
public interface MatcherApi<T> {
    List<VariableAssignment> matchLabel(GoalNode<T> currentState, String label);

    List<VariableAssignment> matchSeq(GoalNode<T> currentState, String data, Signature sig);

}
