/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * The class ASTUtil is a collection of static method for operation on DafnyTrees.
 *
 * @see DafnyTree
 *
 * @author Mattias Ulbrich
 */
public final class ASTUtil {

    private ASTUtil() {
        throw new Error();
    }

    /**
     * Creates an AST for the negation of a formula.
     *
     * @param cond the AST for a formula
     * @return the AST for the negated formula.
     */
    public static DafnyTree negate(DafnyTree cond) {
        DafnyTree result = new DafnyTree(DafnyParser.NOT, "not");
        result.addChild(cond);
        return result;
    }

    /**
     * Gets the label for the proof obligation in this object.
     *
     * @param tree
     *            a non-<code>null</code> ast node
     * @return the label, could be <code>null</code>
     */
    public static String getLabel(DafnyTree tree) {
        DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
        if (label != null) {
            return label.getLastChild().toString();
        }
        return null;
    }

    /**
     * Returns a constant tree for the <code>null</code> literal.
     *
     * @return a freshly created tree
     */
    // Checkstyle: IGNORE MethodNameCheck
    public static DafnyTree _null() {
        return new DafnyTree(DafnyParser.NULL, "null");
    }

    /**
     * Returns a tree for an equality on asts.
     *
     * @param tree1 the lhs of the equality, not <code>null</code>
     * @param tree2 the rhs of the equality, not <code>null</code>
     * @return a freshly created tree
     */
    public static DafnyTree equals(DafnyTree tree1, DafnyTree tree2) {
        DafnyTree result = new DafnyTree(DafnyParser.EQ, "=");
        result.addChild(tree1);
        result.addChild(tree2);
        return result;
    }

    /**
     * Returns a tree for a "Not equals" expression.
     *
     * @param tree1 the lhs of the inequality, not <code>null</code>
     * @param tree2 the rhs of the inequality, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree notEquals(DafnyTree tree1, DafnyTree tree2) {
        DafnyTree result = new DafnyTree(DafnyParser.NEQ, "!=");
        result.addChild(tree1);
        result.addChild(tree2);
        return result;
    }

    /**
     * Returns a tree for a conjunction on ast trees.
     *
     * @param conj1 the first conjunct, not <code>null</code>
     * @param conj2 the second conjunct, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree and(DafnyTree conj1, DafnyTree conj2) {
        DafnyTree result = new DafnyTree(DafnyParser.AND, "&&");
        result.addChild(conj1);
        result.addChild(conj2);
        return result;
    }

    /**
     * Returns a tree for a conjunction with arbitrary many conjuncts.
     *
     * The result is associated to the left, e.g., <code>and(a,b,c)</code>
     * results in <code>(&& (&& a b) c)</code>.
     *
     * If the collection is a singleton, the sole argument is returned.
     *
     * @throws IllegalArgumentException
     *             if {@code trees} is empty
     * @param trees
     *            a non-<code>null</code> collection of conjuncts
     * @return a possibly freshy created dafny tree
     */
    public static DafnyTree and(Iterable<DafnyTree> trees) {

        DafnyTree result = new DafnyTree(DafnyParser.AND, "&&");
        for (DafnyTree tree : trees) {
            if (result.getChildCount() == 2) {
                DafnyTree t = new DafnyTree(DafnyParser.AND, "&&");
                t.addChild(result);
                result = t;
            }
            result.addChild(tree);
        }

        if (result.getChildCount() == 0) {
            throw new IllegalArgumentException("Empty conjunction not supported");
        }

        if (result.getChildCount() == 1) {
            result = result.getChild(0);
        }

        return result;
    }

    /**
     * Returns an implication of DafnyTrees.
     *
     * @param premiss
     *            the ast for the premiss, not <code>null</code>
     * @param concl
     *            the ast for the conclusion, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree impl(DafnyTree premiss, DafnyTree concl) {
        DafnyTree result = new DafnyTree(DafnyParser.IMPLIES, "==>");
        result.addChild(premiss);
        result.addChild(concl);
        return result;
    }

    /**
     * Returns a tree for an integer literal.
     *
     * @param value
     *            the value of the literal
     * @return a freshly created dafny tree
     */
    public static DafnyTree intLiteral(int value) {
        DafnyTree result = new DafnyTree(DafnyParser.INT_LIT, Integer.toString(value));
        return result;
    }

    /**
     * Returns a tree for a ">=" comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree greaterEqual(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.GE, ">=");
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for a "<=" comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree lessEqual(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.LE, "<=");
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for a "<" comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree less(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.LT, "<");
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for a Noetherian termination comparison.
     *
     * @param exp1 the first expression, not <code>null</code>
     * @param exp2 the second expression, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree noetherLess(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(DafnyParser.NOETHER_LESS);
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    /**
     * Returns a tree for the length of an single-dim array.
     *
     * @param array the reference whose length is to be taken, not <code>null</code>
     * @return a freshly created dafny tree
     */
    public static DafnyTree length(DafnyTree array) {
        DafnyTree result = new DafnyTree(DafnyParser.LENGTH, "Length");
        result.addChild(array);
        return result;
    }

    /**
     * Returns an identifier token with the given variable/id name.
     *
     * @param id non-<code>null</code> name of identifier
     * @return a freshly created dafny tree
     */
    public static DafnyTree id(String id) {
        return new DafnyTree(DafnyParser.ID, id);
    }

}
