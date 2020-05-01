/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.dafnystructures.TarjansAlgorithm;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;
import nonnull.Nullable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Function;

public class SymbexExpressionValidator {

    private final Collection<SymbexPath> stack;
    private final SymbexPath state;
    private final boolean checkReads;

    public SymbexExpressionValidator(Collection<SymbexPath> stack, SymbexPath state, boolean checkReads) {
        this.stack = stack;
        this.state = state;
        this.checkReads = checkReads;
    }

    public SymbexExpressionValidator(Collection<SymbexPath> stack, SymbexPath state) {
        this(stack, state, false);
    }

    public static void handleExpression(Collection<SymbexPath> paths, SymbexPath path, DafnyTree expression) {
        SymbexExpressionValidator validator = new SymbexExpressionValidator(paths, path);
        validator.handleExpression(expression);
    }

    private static class ImplicationWrapper implements Function<DafnyTree, DafnyTree> {
        private final DafnyTree premiss;

        private ImplicationWrapper(DafnyTree premiss) {
            this.premiss = premiss;
        }

        @Override
        public DafnyTree apply(DafnyTree dafnyTree) {
            return ASTUtil.impl(premiss, dafnyTree.dupTree());
        }
    }

    private static class UniversalWrapper implements Function<DafnyTree, DafnyTree> {

        private final DafnyTree type;
        private final List<DafnyTree> variables;

        private UniversalWrapper(DafnyTree prototype) {
            this.variables = prototype.getChildren().subList(0, prototype.getChildCount() - 2);
            this.type = prototype.getFirstChildWithType(DafnyParser.TYPE);
        }

        @Override
        public DafnyTree apply(DafnyTree dafnyTree) {
            DafnyTree result = new DafnyTree(DafnyParser.ALL);
            result.addChildren(Util.map(variables, DafnyTree::dupTree));
            if (type != null) {
                result.addChild(type.dupTree());
            }
            result.addChild(dafnyTree.dupTree());
            return result;
        }
    }

    private static class LetWrapper implements Function<DafnyTree, DafnyTree> {

        private final DafnyTree originalLet;

        private LetWrapper(DafnyTree originalLet) {
            this.originalLet = originalLet;
        }

        @Override
        public DafnyTree apply(DafnyTree dafnyTree) {
            DafnyTree result = originalLet.dupTree();
            int lastIndex = result.getChildCount() - 1;
            result.replaceChildren(lastIndex, lastIndex, dafnyTree.dupTree());
            return result;
        }
    }


    /*
     * Handle expressions:
     * - Create runtime checks for array accesses
     *   - non-null
     *   - index in bounds
     * - for field / method accesses
     *   - non-null
     * - add shortcut evaluations as guards as path conditions
     */
    public void handleExpression(DafnyTree expression) {
        handleExpression(expression, x -> x);
    }

    private void handleExpression(DafnyTree expression,
                                  Function<DafnyTree, DafnyTree> wrapper) {
        DafnyTree child0;
        DafnyTree child1;
        DafnyTree child2;
        ImplicationWrapper guard;
        switch (expression.getType()) {
        case DafnyParser.AND:
        case DafnyParser.IMPLIES:
            assert expression.getChildCount() == 2;
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            handleExpression(child0, wrapper);
            guard = new ImplicationWrapper(child0);
            handleExpression(child1, guard.andThen(wrapper));
            break;

        case DafnyParser.OR:
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            handleExpression(child0, wrapper);
            guard = new ImplicationWrapper(ASTUtil.negate(child0));
            handleExpression(child1, guard.andThen(wrapper));
            break;

        case DafnyParser.IF:
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            child2 = expression.getChild(2);
            handleExpression(child0, wrapper);
            // THEN
            guard = new ImplicationWrapper(child0);
            handleExpression(child1, guard.andThen(wrapper));
            // ELSE
            guard = new ImplicationWrapper(ASTUtil.negate(child0));
            handleExpression(child2, guard.andThen(wrapper));
            break;

        case DafnyParser.ARRAY_ACCESS:
            child0 = expression.getChild(0);
            handleExpression(child0, wrapper);
            addNonNullCheck(child0, wrapper);
            addReadsCheck(child0, wrapper);

            for (int i = 1; i < expression.getChildCount(); i++) {
                DafnyTree child = expression.getChild(i);
                String suffix = expression.getChildCount() > 2 ? Integer.toString(i - 1) : "";
                if(child.getType() == DafnyParser.DOTDOT) {
                    // bugfix ...
                    for (int j = 0; j < child.getChildCount(); j++) {
                        DafnyTree index = child.getChild(j);
                        if(index.getType() == DafnyParser.ARGS) {
                            continue;
                        }
                        // TODO perhaps have monotonicity?
                        addIndexInRangeCheck(index, child0, suffix, wrapper);
                        handleExpression(index, wrapper);
                    }
                } else {
                    addIndexInRangeCheck(child, child0, suffix, wrapper);
                    handleExpression(child, wrapper);
                }
            }
            break;

        case DafnyParser.LENGTH:
            child0 = expression.getChild(0);
            addNonNullCheck(child0, wrapper);
            handleExpression(child0, wrapper);
            break;

        case DafnyParser.FIELD_ACCESS:
            child0 = expression.getChild(0);
            addNonNullCheck(child0, wrapper);
            addReadsCheck(child0, wrapper);
            handleExpression(child0, wrapper);
            break;

        case DafnyParser.DIV:
        case DafnyParser.MODULO:
            child0 = expression.getChild(0);
            child1 = expression.getChild(1);
            handleExpression(child0, wrapper);
            handleExpression(child1, wrapper);
            addNotZeroCheck(child1, wrapper);
            break;

        case DafnyParser.CALL:
            handleFunctionCall(expression, wrapper);
            break;

        case DafnyParser.EX:
        case DafnyParser.ALL:
            handleExpression(expression.getLastChild(),
                    new UniversalWrapper(expression).andThen(wrapper));
            break;

        case DafnyParser.LET:
            for (int i = 0; i < expression.getChildCount() - 1; i++) {
                handleExpression(expression.getChild(i), wrapper);
            }
            handleExpression(expression.getLastChild(),
                    new LetWrapper(expression).andThen(wrapper));
            break;

        case DafnyParser.ID:
            if(expression.getDeclarationReference().getType() == DafnyParser.FIELD) {
                addReadsCheck(ASTUtil._this(), wrapper);
            }
            break;

        default:
            for (int i = 0; i < expression.getChildCount(); i++) {
                handleExpression(expression.getChild(i), wrapper);
            }
        }
    }


    private void handleFunctionCall(DafnyTree expression, Function<DafnyTree, DafnyTree> wrapper) {
        DafnyTree callee = expression.getChild(0).getDeclarationReference();
        DafnyTree args = expression.getLastChild();
        DafnyTree receiver = null;
        if(expression.getChildCount() == 3) {
            // there is a receiver
            receiver = expression.getChild(1);
            handleExpression(receiver, wrapper);
            addNonNullCheck(receiver, wrapper);
        }

        for (int i = 0; i < args.getChildCount(); i++) {
            handleExpression(args.getChild(i), wrapper);
        }

        List<Pair<String, DafnyTree>> subs = new ArrayList<>();
        if (receiver != null) {
            subs.add(new Pair<>("this", receiver));
        }
        subs.addAll(ASTUtil.methodParameterSubs(callee, args));

        // ------------------
        // preconditions
        List<DafnyTree> preconds = callee.getChildrenWithType(DafnyParser.REQUIRES);
        for (DafnyTree precond : preconds) {
            SymbexPath reqState = new SymbexPath(state);
            reqState.setBlockToExecute(Symbex.EMPTY_PROGRAM);
            DafnyTree condition = precond.getLastChild();
            // wrap that into a substitution
            condition = ASTUtil.letCascade(subs, condition);
            // and use the wrapper from outside ...
            condition = wrapper.apply(condition);
            reqState.setProofObligation(condition, expression, AssertionType.CALL_PRE);
            stack.add(reqState);
        }

        // ------------------
        // variant if in recursion loop.
        DafnyTree callerSCC = state.getMethod().getExpressionType();
        DafnyTree calleeSCC = callee.getExpressionType();
        assert callerSCC.getType() == TarjansAlgorithm.CALLGRAPH_SCC
                && calleeSCC.getType() == TarjansAlgorithm.CALLGRAPH_SCC;
        if(callerSCC.getText().equals(calleeSCC.getText())) {
            // both in same stron. conn. component ==> potential cycle
            DafnyTree calleeDecr = callee.getFirstChildWithType(DafnyParser.DECREASES);
            if(calleeDecr == null) {
                calleeDecr = ASTUtil.intLiteral(0);
                // TODO rather throw an exception?
            } else {
                calleeDecr = calleeDecr.getLastChild();
                // wrap that into a substitution
                calleeDecr = ASTUtil.letCascade(subs, calleeDecr);
            }

            DafnyTree callerDecr = state.getMethod().getFirstChildWithType(DafnyParser.DECREASES);
            if (callerDecr == null) {
                callerDecr = ASTUtil.intLiteral(0);
                // TODO rather throw an exception?
            } else {
                callerDecr = calleeDecr.getLastChild();
            }

            DafnyTree condition = ASTUtil.noetherLess(
                    ASTUtil.create(DafnyParser.LISTEX, calleeDecr),
                    ASTUtil.create(DafnyParser.LISTEX, callerDecr));

            // and use the wrapper from outside ...
            condition = wrapper.apply(condition);
            SymbexPath decrState = new SymbexPath(state);
            decrState.setBlockToExecute(Symbex.EMPTY_PROGRAM);
            decrState.setProofObligation(condition, expression, AssertionType.VARIANT_DECREASED);
            stack.add(decrState);
        }
    }

    private void addIndexInRangeCheck(DafnyTree idx, @Nullable DafnyTree array,
                                     String arrayLengthSuffix,
                                      Function<DafnyTree, DafnyTree> wrapper) {
        SymbexPath bounds = new SymbexPath(state);
        DafnyTree check = ASTUtil.lessEqual(ASTUtil.intLiteral(0), idx);
        if (array != null) {
            check = ASTUtil.and(check, ASTUtil.less(idx, ASTUtil.length(array, arrayLengthSuffix)));
        }
        check = wrapper.apply(check);
        bounds.setProofObligation(check, idx, AssertionType.RT_IN_BOUNDS);
        bounds.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        stack.add(bounds);
    }

    private void addNonNullCheck(DafnyTree expression, Function<DafnyTree, DafnyTree> wrapper) {
        if (expression.getType() == DafnyParser.THIS) {
            // No check for explicit this references ...
            return;
        }

        if (expression.getExpressionType().getText().equals("seq")) {
            // No check for seq, olny for array.
            return;
        }

        SymbexPath nonNull = new SymbexPath(state);
        DafnyTree check = ASTUtil.notEquals(expression.dupTree(), ASTUtil._null());
        nonNull.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        check = wrapper.apply(check);
        nonNull.setProofObligation(check, expression, AssertionType.RT_NONNULL);

        stack.add(nonNull);
    }

    private void addReadsCheck(DafnyTree expression, Function<DafnyTree, DafnyTree> wrapper) {
        if (!checkReads) {
            // reads checks are optional and only for functions!
            return;
        }

        if (expression.getType() != DafnyParser.THIS &&
                expression.getExpressionType().getText().equals("seq")) {
            // No check for seq, olny for array.
            return;
        }

        SymbexPath path = new SymbexPath(state);
        DafnyTree check = ASTUtil.inMod(expression);
        check = wrapper.apply(check);
        path.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        path.setProofObligation(check, expression, AssertionType.READS);

        stack.add(path);
    }

    private void addNotZeroCheck(DafnyTree size, Function<DafnyTree,DafnyTree> wrapper) {
        SymbexPath bounds = new SymbexPath(state);
        DafnyTree check = ASTUtil.notEquals(size, ASTUtil.intLiteral(0));
        check = wrapper.apply(check);
        bounds.setProofObligation(check, size, AssertionType.RT_DIV0);
        bounds.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        stack.add(bounds);
    }

}
