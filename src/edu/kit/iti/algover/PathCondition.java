package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.PseudoTree;


public class PathCondition {

    public enum AssertionType {
        CALL_PRE, ASSERT, POST, INVARIANT_PRESERVED, INVARIANT_INITIALLY_VALID;
    }

    public enum AssumptionType {
        PRE, IF_THEN, IF_ELSE, CALL_POST, WHILE_TRUE, WHILE_FALSE, POST, ASSUMED_INVARIANT;
    }

    private VariableMap state;
    private PseudoTree expression;
    private PseudoTree refersTo;
    private AssumptionType type;

    public PathCondition(PseudoTree expression, PseudoTree refersTo, AssumptionType type, VariableMap state) {
        this.refersTo = refersTo;
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

    public PseudoTree getInstantiatedExpression() {
        return state.instantiate(expression);
    }

}
