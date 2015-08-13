package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.PseudoTree;


public class PathCondition {

    public enum AssertionType {
        CALL_PRE, ASSERT, POST, ASSERTED_INVARIANT;
    }

    public enum AssumptionType {
        PRE, IF_THEN, IF_ELSE, CALL_POST, WHILE_TRUE, WHILE_FALSE, POST, ASSUMED_INVARIANT;
    }

    private VariableMap state;
    private PseudoTree expression;
    private AssumptionType type;

    public PathCondition(PseudoTree expression, AssumptionType type, VariableMap state) {
        this.expression = expression;
        this.type = type;
        this.state = state;
    }

    public AssumptionType getType() {
        return type;
    }

    public VariableMap getMap() {
        return state;
    }

    public PseudoTree getExpression() {
        return expression;
    }

}
