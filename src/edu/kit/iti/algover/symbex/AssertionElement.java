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
public class AssertionElement {

    /**
     * There are different reasons for assertions.
     */
    public enum AssertionType {
        /**
         * Precondition to be checked prior to method invocation.
         */
        CALL_PRE,

        /**
         * Explicit assertion.
         */
        EXPLICIT_ASSERT,

        /**
         * Implicit assertion (div by zero, null-access, in range, ...)
         */
        IMPLICIT_ASSERT,

        /**
         * Postcondition to be proved.
         */
        POST,

        /**
         * Loop Invariant to be proved inductive.
         */
        INVARIANT_PRESERVED,

        /**
         * Loop Invariant has to hold initially.
         */
        INVARIANT_INITIALLY_VALID,

        /**
         * Runtime Assertion: Receiver is different from null
         */
        RT_NONNULL,

        /**
         * Runtime Assertion: Array/Sequence index in bounds of receiver
         */
        RT_IN_BOUNDS;
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
    private final AssertionType type;

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
    public AssertionElement(DafnyTree expression,
            DafnyTree refersTo, AssertionType type, VariableMap state) {

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
    public AssertionType getType() {
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
