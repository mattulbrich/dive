/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

public class ASTUtil {

    private ASTUtil() {
        throw new Error();
    }

    /**
     * Create an AST for the negation of a formula
     *
     * @param cond the AST for a formula
     * @return the AST for the negated formula.
     */
    public static DafnyTree negate(DafnyTree cond) {
        DafnyTree result= new DafnyTree(new CommonToken(DafnyParser.NOT, "not"));
        result.addChild(cond);
        return result;
    }

    public static String getLabel(DafnyTree tree) {
        DafnyTree label = tree.getFirstChildWithType(DafnyParser.LABEL);
        if(label != null) {
            return label.getLastChild().toString();
        }
        return null;
    }

    public static DafnyTree _null() {
        return new DafnyTree(new CommonToken(DafnyParser.NULL, "null"));
    }

    public static DafnyTree equals(DafnyTree tree1, DafnyTree tree2) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.EQ, "="));
        result.addChild(tree1);
        result.addChild(tree2);
        return result;
    }

    public static DafnyTree notEquals(DafnyTree tree1, DafnyTree tree2) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.NEQ, "!="));
        result.addChild(tree1);
        result.addChild(tree2);
        return result;
    }

    public static DafnyTree and(DafnyTree conj1, DafnyTree conj2) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.AND, "&&"));
        result.addChild(conj1);
        result.addChild(conj2);
        return result;
    }

    public static DafnyTree and(Iterable<DafnyTree> trees) {

        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.AND, "&&"));
        for (DafnyTree tree : trees) {
            if(result.getChildCount() == 2) {
                DafnyTree t = new DafnyTree(new CommonToken(DafnyParser.AND, "&&"));
                t.addChild(result);
                result = t;
            }
            result.addChild(tree);
        }

        if(result.getChildCount() == 0) {
            throw new IllegalArgumentException("Empty conjunction not supported");
        }

        if(result.getChildCount() == 1) {
            result = result.getChild(0);
        }

        return result;
    }

    public static DafnyTree impl(DafnyTree premiss, DafnyTree concl) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.IMPLIES, "==>"));
        result.addChild(premiss);
        result.addChild(concl);
        return result;
    }

    public static DafnyTree intLiteral(int value) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.LIT, Integer.toString(value)));
        return result;
    }

    public static DafnyTree greaterEqual(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.GE, ">="));
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    public static DafnyTree lessEqual(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.LE, "<="));
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    public static DafnyTree less(DafnyTree exp1, DafnyTree exp2) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.LT, "<"));
        result.addChild(exp1);
        result.addChild(exp2);
        return result;
    }

    public static DafnyTree length(DafnyTree array) {
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.LENGTH, "Length"));
        result.addChild(array);
        return result;
    }

}
