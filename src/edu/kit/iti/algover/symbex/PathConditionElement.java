/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.util.ASTUtil;

/**
 * The Class PathCondition captures a single element of a path condition.
 *
 * This is one formula with a variable assignment and the type of the condition.
 *
 * Instances of this class are immutable.
 *
 * @author mattias ulbrich
 */
public class PathConditionElement {

    /**
     * AssumptionType enumerate all possible kinds that a path condition may
     * have.
     */
    public enum AssumptionType {
        /**
         * The condition is a clause in a precondition.
         */
        PRE,
        /**
         * The condition is a positive if-condition (then branch).
         */
        IF_THEN,
        /**
         * The condition is a negative if-condition (else branch).
         */
        IF_ELSE,
        /**
         * The condition is an assumed post condition of a function call.
         */
        CALL_POST,
        /**
         * The condition is a positive while-condition (body preserves case).
         */
        WHILE_TRUE,
        /**
         * The condition is a negative while-condition (use case).
         */
        WHILE_FALSE,
        /**
         * The condition is an assumed loop invariant.
         */
        ASSUMED_INVARIANT,
        /**
         * The condition is an explicit assume statement
         */
        EXPLICIT_ASSUMPTION,
        /**
         * The condition is an assumed assertion after it has been proved.
         */
        ASSUMED_ASSERTION,
        /**
         * The condition comes from a guard during short-circuit evaluation.
         *
         * In a ==> b, a guards the well-definedness of b, e.g.
         */
        GUARD_IN_EXPRESSION;
    }

    /**
     * The state in which the condition is evaluated.
     */
    private VariableMap state;

    /**
     * The expression (first order formula) of this path condition.
     */
    private final DafnyTree expression;

    /**
     * The syntactical element (subtree) to which this path condition element
     * refers to.
     *
     * For {@link AssumptionType#IF_THEN} that is the if statement and for
     * {@link AssumptionType#PRE} that is the requires clause, etc.
     */
    private final DafnyTree refersTo;

    /**
     * The type of this condition element.
     */
    private final AssumptionType type;

    /**
     * Instantiates a new path condition element.
     *
     * @param expression
     *            the expression of the condition
     * @param refersTo
     *            the syntax element to refer to
     * @param type
     *            the type of the element
     * @param state
     *            the state in which it is explored
     */
    public PathConditionElement(DafnyTree expression,
            DafnyTree refersTo, AssumptionType type, VariableMap state) {

        assert expression != null;
        assert type != null;
        assert state != null;
        assert refersTo != null;

        this.refersTo = refersTo;
        this.expression = expression;
        this.type = type;
        this.state = state;
    }

    /**
     * Gets the type of the condition element.
     *
     * @return the type of this expression, not <code>null</code>.
     */
    public AssumptionType getType() {
        return type;
    }

    /**
     * Gets the variable map for the expression.
     *
     * @return the variable assignment, not <code>null</code>.
     */
    public VariableMap getVariableMap() {
        return state;
    }

    /**
     * Gets the formula/expression of this condition.
     *
     * @return the expression, not <code>null</code>
     */
    public DafnyTree getExpression() {
        return expression;
    }

    /**
     * Gets the expression instantiated with the variable mapping.
     *
     * Replaces all program variables in the expression according to the variable map.
     *
     * @return the instantiated expression, not <code>null</code>
     */
    public DafnyTree getInstantiatedExpression() {
        return state.instantiate(expression);
    }

    /**
     * Gets the name for this condition as specified in the code.
     *
     * Currently, <code>null</code> can be returned if no label has been
     * specified
     *
     * @return the name of the path condition element, <code>null</code> if none
     *         specified.
     */
    public String getName() {
        return ASTUtil.getLabel(refersTo);
    }

}
