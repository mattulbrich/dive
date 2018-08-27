/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ASTUtil;
import nonnull.Nullable;

import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

public class SymbexExpressionValidator {

    /*
     * Handle expressions:
     * - Create runtime checks for array accesses
     *   - non-null
     *   - index in bounds
     * - for field / method accesses
     *   - non-null
     * - add shortcut evaluations as guards as path conditions
     */
    public void handleExpression(Deque<SymbexPath> stack, SymbexPath current,
                                  DafnyTree expression) {

        DafnyTree child0;
        DafnyTree child1;
        DafnyTree child2;
        switch (expression.getType()) {
        case DafnyParser.AND:
        case DafnyParser.IMPLIES:
            assert expression.getChildCount() == 2;
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            handleExpression(stack, current, child0);
            SymbexPath guarded = new SymbexPath(current);
            guarded.addPathCondition(child0, child0, AssumptionType.GUARD_IN_EXPRESSION);
            handleExpression(stack, guarded, child1);
            break;

        case DafnyParser.OR:
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            handleExpression(stack, current, child0);
            guarded = new SymbexPath(current);
            guarded.addPathCondition(ASTUtil.negate(child0),
                    child0, AssumptionType.GUARD_IN_EXPRESSION);
            handleExpression(stack, guarded, child1);
            break;

        case DafnyParser.IF:
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            child2 = expression.getChild(2);
            handleExpression(stack, current, child0);
            // THEN
            guarded = new SymbexPath(current);
            guarded.addPathCondition(child0,
                    child0, AssumptionType.GUARD_IN_EXPRESSION);
            handleExpression(stack, guarded, child1);
            // ELSE
            guarded = new SymbexPath(current);
            guarded.addPathCondition(ASTUtil.negate(child0),
                    child0, AssumptionType.GUARD_IN_EXPRESSION);
            handleExpression(stack, guarded, child2);
            break;

        case DafnyParser.ARRAY_ACCESS:
            child0 = expression.getChild(0);
            handleExpression(stack, current, child0);
            addNonNullCheck(stack, current, child0);

            for (int i = 1; i < expression.getChildCount(); i++) {
                DafnyTree child = expression.getChild(i);
                String suffix = expression.getChildCount() > 2 ? Integer.toString(i - 1) : "";
                addIndexInRangeCheck(stack, current, child, child0, suffix);
                handleExpression(stack, current, child);
            }
            break;

        case DafnyParser.LENGTH:
        case DafnyParser.FIELD_ACCESS:
            child0 = expression.getChild(0);
            addNonNullCheck(stack, current, child0);
            handleExpression(stack, current, child0);
            break;

        case DafnyParser.DIV:
        case DafnyParser.MODULO:
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            handleExpression(stack, current, child0);
            handleExpression(stack, current, child1);
            addNotZeroCheck(stack, current, child1);
            break;

        case DafnyParser.CALL:
            System.out.println(">> " + expression.toStringTree());


        default:
            for (int i = 0; i < expression.getChildCount(); i++) {
                handleExpression(stack, current, expression.getChild(i));
            }
        }
    }

    private void addIndexInRangeCheck(Deque<SymbexPath> stack, SymbexPath current,
                                     DafnyTree idx, @Nullable DafnyTree array,
                                     String arrayLengthSuffix) {
        SymbexPath bounds = new SymbexPath(current);
        List<DafnyTree> pos = new ArrayList<>();
        /// FIXME! Make this unidirectional!
        pos.add(ASTUtil.greaterEqual(idx, ASTUtil.intLiteral(0)));
        if (array != null) {
            pos.add(ASTUtil.less(idx, ASTUtil.length(array, arrayLengthSuffix)));
        }
        bounds.setProofObligations(pos, idx, AssertionType.RT_IN_BOUNDS);
        bounds.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        stack.push(bounds);
    }

    private void addNonNullCheck(Deque<SymbexPath> stack, SymbexPath current,
                                 DafnyTree expression) {
        SymbexPath nonNull = new SymbexPath(current);
        if (expression.getType() == DafnyParser.THIS) {
            // No check for explicit this references ...
            return;
        }
        if (expression.getExpressionType().getText().equals("seq")) {
            // No check for seq, olny for array.
            return;
        }
        DafnyTree check = ASTUtil.notEquals(expression, ASTUtil._null());
        nonNull.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        nonNull.setProofObligation(check, expression, AssertionType.RT_NONNULL);
        stack.push(nonNull);
    }

    private void addNotZeroCheck(Deque<SymbexPath> stack, SymbexPath current,
                                  DafnyTree size) {
        SymbexPath bounds = new SymbexPath(current);
        List<DafnyTree> pos = new ArrayList<>();
        pos.add(ASTUtil.notEquals(size, ASTUtil.intLiteral(0)));
        bounds.setProofObligations(pos, size, AssertionType.RT_IN_BOUNDS);
        bounds.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        stack.push(bounds);
    }

}
