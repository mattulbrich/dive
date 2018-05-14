/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyParser;
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
     */
    public AssertionElement(DafnyTree expression, DafnyTree refersTo, AssertionType type) {

        assert expression != null;
        assert type != null;
        assert refersTo != null;

        this.refersTo = refersTo;
        this.expression = expression;
        this.type = type;
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
        if(refersTo.getType() == DafnyParser.CALL) {
            // method name if this induced by a method call ...
            return refersTo.getChild(0).getText();
        }
        return ASTUtil.getLabel(refersTo);
    }

    public DafnyTree getOrigin() {
        return refersTo;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        String name = getName();
        String suffix = name == null ? "" : "[" + name + "]";
        return getType() + suffix + ":" + expression.toStringTree();
    }

    /**
     * Gets the suffix which is added to the PCV label.
     *
     * @return the assertion type and a label if present.
     */
    public String getPVCLabelSuffix() {
        String name = getName();
        String suffix = name == null ? "" : "[" + name + "]";
        return getType().identifier + suffix;
    }

    /**
     * There are different reasons for assertions.
     */
    public enum AssertionType {
        /**
         * Precondition to be checked prior to method invocation.
         */
        CALL_PRE("EstPre"),

        /**
         * Explicit assertion.
         */
        EXPLICIT_ASSERT("Assert"),

        /**
         * Postcondition to be proved.
         */
        POST("Post"),

        /**
         * Loop Invariant to be proved inductive.
         */
        INVARIANT_PRESERVED("Inv"),

        /**
         * Loop Invariant has to hold initially.
         */
        INVARIANT_INITIALLY_VALID("InitInv"),

        /**
         * Runtime Assertion: Receiver is different from null.
         */
        RT_NONNULL("Null"),

        /**
         * Runtime Assertion: Array/Sequence index in bounds of receiver.
         */
        RT_IN_BOUNDS("Bounds"),

        /**
         * Variant / measured by reduced.
         */
        VARIANT_DECREASED("Dec"),

        /**
         * Assigned object is in the "modifies" set.
         */
        MODIFIES("Modifies");

        /**
         * The identifier used when constructing a UI-string for a symbex path.
         */
        public final String identifier;

        AssertionType(String identifier) {
            this.identifier = identifier;
        }
    }

}
