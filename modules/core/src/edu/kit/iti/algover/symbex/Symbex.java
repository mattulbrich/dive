/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.ImmutableList;

/**
 * Symbex can be used to perform symbolic execution on a function.
 *
 * Create an instance and apply {@link #symbolicExecution(DafnyTree)}.
 *
 * The handle-methods are package visible to allow for testing from within
 * the package.
 */
public class Symbex {

    /**
     * The designated variable that represents the heap.
     */
    public static final String HEAP_VAR = "#h";

    /**
     * The designated variable that represents decreases clauses.
     */
    public static final String DECREASES_VAR = "#d";

    /**
     * The Constant EMPTY_PROGRAM points to an empty AST.
     */
    private static final DafnyTree EMPTY_PROGRAM =
            new DafnyTree(DafnyParser.BLOCK);

    /**
     * Performs symbolic execution on a function.
     *
     * It returns all proof obligations which arise during this execution. At
     * the moment, the process is neither scriptable nor configurable.
     *
     * @param function
     *            the function to execute, not <code>null</code>
     * @return a freshly created list of symbolic execution states, not
     *         <code>null</code>
     */
    public List<SymbexPath> symbolicExecution(DafnyTree function) {

        assert function.getType() == DafnyParser.METHOD;
        SymbexPath initial = makeFromPreconditions(function);

        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();

        stack.add(initial);

        while (!stack.isEmpty()) {
            SymbexPath state = stack.removeFirst();

            assert state.getBlockToExecute().getType() == DafnyParser.BLOCK;

            if (state.getBlockToExecute().getChildCount() == 0) {
                results.add(state);
            } else {

                DafnyTree stm = state.getBlockToExecute().getChild(0);
                DafnyTree remainder = makeRemainderTree(state.getBlockToExecute());

                switch(stm.getType()) {
                case DafnyParser.ARRAY_UPDATE:
                    handleArrayUpdate(stack, state, stm, remainder);
                    break;

                case DafnyParser.ASSIGN:
                    handleAssign(stack, state, stm, remainder);
                    break;

                case DafnyParser.VAR:
                    handleVarDecl(stack, state, stm, remainder);
                    break;

                case DafnyParser.WHILE:
                    handleWhile(stack, state, stm, remainder);
                    break;

                case DafnyParser.IF:
                    handleIf(stack, state, stm, remainder);
                    break;

                case DafnyParser.ASSERT:
                    handleAssert(stack, state, stm, remainder);
                    break;

                case DafnyParser.ASSUME:
                    handleAssume(stack, state, stm, remainder);
                    break;

                case DafnyParser.HAVOC:
                    handleHavoc(stack, state, stm, remainder);
                    break;

                default:
                    throw new UnsupportedOperationException("Unknown code: "
                                + DafnyParser.tokenNames[stm.getType()]);
                }
            }
        }

        return results;
    }

    /*
     * Handle an assert statement.
     *
     * This adds a proof obligation to the results and the remainder of the
     * program onto the stack. The state remains untouched.
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleAssert(Deque<SymbexPath> stack,
            SymbexPath state, DafnyTree stm,
            DafnyTree remainder) {
        SymbexPath assertedState = new SymbexPath(state);
        assertedState.setBlockToExecute(EMPTY_PROGRAM);
        assertedState.setProofObligation(stm.getLastChild(), stm, AssertionType.EXPLICIT_ASSERT);
        stack.add(assertedState);
        state.setBlockToExecute(remainder);
        state.addPathCondition(stm.getLastChild(), stm, AssumptionType.ASSUMED_ASSERTION);
        stack.add(state);
    }

    /*
     * Handle an assume statement
     * This adds a hypothesis to the proof obligation
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleAssume(Deque<SymbexPath> stack,
            SymbexPath state, DafnyTree stm,
            DafnyTree remainder) {
        SymbexPath assumedState = new SymbexPath(state);
        assumedState.addPathCondition(stm.getLastChild(), stm, AssumptionType.EXPLICIT_ASSUMPTION);
        assumedState.setBlockToExecute(remainder);
        stack.add(assumedState);
    }

    /*
     * Handle an if statement.
     *
     * Two new states are pushed onto the stack for each branch. Path condition
     * elements are added according to the decision expression.
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleIf(Deque<SymbexPath> stack, SymbexPath state,
            DafnyTree stm, DafnyTree remainder) {
        DafnyTree cond = stm.getChild(0);
        handleExpression(stack, state, cond);

        DafnyTree then = stm.getChild(1);
        SymbexPath stateElse = new SymbexPath(state);
        state.addPathCondition(cond, stm, AssumptionType.IF_THEN);
        state.setBlockToExecute(append(then, remainder));
        stack.push(state);
        stateElse.addPathCondition(ASTUtil.negate(cond), stm, AssumptionType.IF_ELSE);
        if (stm.getChildCount() == 3) {
            DafnyTree elseStm = stm.getChild(2);
            stateElse.setBlockToExecute(append(elseStm, remainder));
        } else {
            stateElse.setBlockToExecute(remainder);
        }
        stack.push(stateElse);
    }

    /*
     * Handle a while statement.
     *
     * Three things happen:
     * 1. a PO for the initial validity is added to the results.
     * 2. a symbex target for the preservation of the invariant is added to the stack
     * 3. a symbex target is added for the continuation of the program after the loop.
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleWhile(Deque<SymbexPath> stack,
            SymbexPath state, DafnyTree stm,
            DafnyTree remainder) {
        boolean isLabel = stm.getChild(0).getType() == DafnyParser.LABEL;
        DafnyTree guard = stm.getChild(isLabel ? 1 : 0);
        DafnyTree body = stm.getLastChild();
        DafnyTree decreasesClause = stm.getFirstChildWithType(DafnyParser.DECREASES);
        DafnyTree decreases = toListExt(decreasesClause);
        List<DafnyTree> invariants = stm.getChildrenWithType(DafnyParser.INVARIANT);

        // 1. initially valid.
        SymbexPath invState = new SymbexPath(state);
        invState.setBlockToExecute(EMPTY_PROGRAM);
        invState.setProofObligationsFromLastChild(invariants,
                AssertionType.INVARIANT_INITIALLY_VALID);
        stack.add(invState);

        // 2. preserves invariant:
        // 2a. assume invariants
        SymbexPath preserveState = new SymbexPath(state);
        VariableMap preserveMap = preserveState.getMap();
        String decreaseVar = determineDecreaseVar(preserveMap);
        preserveMap = anonymise(preserveMap, body);
        preserveMap = preserveMap.assign(decreaseVar, decreases);
        preserveState.setMap(preserveMap);
        for (DafnyTree inv : invariants) {
            preserveState.addPathCondition(inv.getLastChild(), inv,
                    AssumptionType.ASSUMED_INVARIANT);
        }

        // guard well-def
        handleExpression(stack, preserveState, guard);

        preserveState.addPathCondition(guard, stm, AssumptionType.WHILE_TRUE);
        preserveState.setBlockToExecute(stm.getLastChild());

        // 2b. show invariants:
        preserveState.setProofObligationsFromLastChild(invariants,
                AssertionType.INVARIANT_PRESERVED);

        // 2c. show decreases clause:
        DafnyTree decrReduced = ASTUtil.noetherLess(ASTUtil.id(decreaseVar), decreases);
        AssertionElement decrProof = new AssertionElement(decrReduced, decreasesClause,
                AssertionType.VARIANT_DECREASED, preserveState.getMap());
        ImmutableList<AssertionElement> oldPOs = preserveState.getProofObligations();
        preserveState.setProofObligations(oldPOs.append(decrProof));
        stack.add(preserveState);

        // 3. use case:
        state.setMap(anonymise(state.getMap(), body));
        for (DafnyTree inv : invariants) {
            state.addPathCondition(inv.getLastChild(), inv, AssumptionType.ASSUMED_INVARIANT);
        }
        state.addPathCondition(ASTUtil.negate(guard), stm, AssumptionType.WHILE_FALSE);
        state.setBlockToExecute(remainder);
        stack.add(state);
    }

    /*
     * Put decreases list into a list expression
     */
    private DafnyTree toListExt(DafnyTree decreases) {
        DafnyTree list = new DafnyTree(DafnyParser.LISTEX);
        list.addChildren(decreases.getChildren());
        return list;
    }

    /*
     * Find the first decreases variable which has not been assigned to.
     */
    private String determineDecreaseVar(VariableMap map) {

        int no = 0;
        String varName = DECREASES_VAR;
        while (map.hasAssignmentTo(varName)) {
            varName = DECREASES_VAR + no;
            no++;
        }

        return varName;
    }

    /*
     * Handle an assignment.
     *
     * This updates the symbex state and pushes it onto the stack.
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleAssign(Deque<SymbexPath> stack, SymbexPath state,
            DafnyTree stm, DafnyTree remainder) {
        String name = stm.getChild(0).toString();
        DafnyTree expression = stm.getChild(1);
        handleExpression(stack, state, expression);
        VariableMap newMap = state.getMap().assign(name, expression);
        state.setMap(newMap);
        state.setBlockToExecute(remainder);
        stack.push(state);
    }

    /*
     * Handle an anyomisation
     *
     * update the state and push it back on the stack
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    private void handleHavoc(Deque<SymbexPath> stack, SymbexPath state,
            DafnyTree stm, DafnyTree remainder) {
        String name = stm.getChild(0).toString();
        VariableMap newMap = state.getMap().anonymise(name);
        state.setMap(newMap);
        state.setBlockToExecute(remainder);
        stack.push(state);
    }

    /*
     * Handle an assignment of the form a[i] := v
     *
     * This updates the symbex state and pushes it onto the stack.
     * The variable that is chaned is Symbex#HEAP_VAR.
     * The statement stands in for the heap update expression
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleArrayUpdate(Deque<SymbexPath> stack, SymbexPath state,
            DafnyTree stm, DafnyTree remainder) {
        String name = HEAP_VAR;
        DafnyTree expression = stm;
        VariableMap newMap = state.getMap().assign(name, expression);
        state.setMap(newMap);
        state.setBlockToExecute(remainder);
        stack.push(state);
    }

    /*
     * Handle a variable declaration.
     *
     * If the variable declaration has an initialisation this is like an
     * assignment.
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleVarDecl(Deque<SymbexPath> stack, SymbexPath state,
            DafnyTree stm, DafnyTree remainder) {
        if (stm.getChildCount() >= 3) {
            String name = stm.getChild(0).toString();
            DafnyTree expression = stm.getChild(2);
            VariableMap newMap = state.getMap().assign(name, expression);
            state.setMap(newMap);
        }
        state.setBlockToExecute(remainder);
        stack.push(state);
    }

    /**
     * Anonymise the variables which are touched in a loop body.
     *
     * @param map
     *            the initial variable map
     * @param body
     *            the body to analyse
     * @return the updated variable map
     */
    private VariableMap anonymise(VariableMap map, DafnyTree body) {
        Set<String> vars = new HashSet<String>();
        collectAssignedVars(body, vars);
        for (String var : vars) {
            map = map.anonymise(var);
        }
        return map;
    }

    /**
     * Collect all variables assigned in a statement block.
     *
     * These are all targets of assignments or function calls.
     *
     * @param tree
     *            the tree to walk over
     * @param vars
     *            the set of variables to which to add found instances.
     */
    private void collectAssignedVars(DafnyTree tree, Set<String> vars) {
        switch(tree.getType()) {
        case DafnyParser.ASSIGN:
            vars.add(tree.getChild(0).toString());
            break;
        case DafnyParser.ARRAY_UPDATE:
            vars.add(HEAP_VAR);
            break;
        case DafnyParser.CALL:
            // TODO revise
            DafnyTree res = tree.getFirstChildWithType(DafnyParser.RESULTS);
            for (DafnyTree r : res.getChildren()) {
                vars.add(r.toString());
            }
            break;
        default:
            List<DafnyTree> children = tree.getChildren();
            if (children != null) {
                for (DafnyTree r : children) {
                    collectAssignedVars(r, vars);
                }
            }
            break;
        }
    }

    /**
     * Combine two statements or blocks into one statement block.
     *
     * The result is guaranteed to be a statement block even if it may contain
     * only one statement (or none).
     *
     * @param prog1
     *            the first statment / statement block
     * @param prog2
     *            the second statment / statement block
     * @return the combined statement block
     */
    private DafnyTree append(DafnyTree prog1, DafnyTree prog2) {
        DafnyTree result = new DafnyTree(DafnyParser.BLOCK);

        if (prog1.getType() == DafnyParser.BLOCK) {
            for (int i = 0; i < prog1.getChildCount(); i++) {
                result.addChild(prog1.getChild(i));
            }
        } else {
            result.addChild(prog1);
        }

        if (prog2.getType() == DafnyParser.BLOCK) {
            for (int i = 0; i < prog2.getChildCount(); i++) {
                result.addChild(prog2.getChild(i));
            }
        } else {
            result.addChild(prog2);
        }

        return result;
    }

    /**
     * Make remainder tree from a statement block.
     *
     * Returns an empty block if the block is already empty.
     *
     * @param block
     *            the block to remove the first element from. May be empty, not
     *            <code>null</code>
     * @return the statement block with the first element removed.
     */
    private DafnyTree makeRemainderTree(DafnyTree block) {

        assert block.getType() == DafnyParser.BLOCK;

        DafnyTree result = new DafnyTree(DafnyParser.BLOCK);
        for (int i = 1; i < block.getChildCount(); i++) {
            result.addChild(block.getChild(i));
        }

        return result;
    }

    /**
     * Create the initial symbolic execution state from the preconditions.
     *
     * @param function
     *            the function to analyse
     * @return the initial symbolic execution state
     */
    private SymbexPath makeFromPreconditions(DafnyTree function) {
        SymbexPath result = new SymbexPath(function);

        for (DafnyTree req : function.getChildrenWithType(DafnyParser.REQUIRES)) {
            result.addPathCondition(req.getLastChild(), req, AssumptionType.PRE);
        }

        result.setBlockToExecute(function.getLastChild());
        result.setProofObligationsFromLastChild(
                function.getChildrenWithType(DafnyParser.ENSURES),
                AssertionType.POST);

        return result;
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
    private void handleExpression(Deque<SymbexPath> stack, SymbexPath current,
            DafnyTree expression) {

        switch(expression.getType()) {
        case DafnyParser.AND:
        case DafnyParser.IMPLIES:
            assert expression.getChildCount() == 2;
            DafnyTree child0 = expression.getChild(0);
            handleExpression(stack, current, child0);
            SymbexPath guarded = new SymbexPath(current);
            guarded.addPathCondition(child0, child0, AssumptionType.GUARD_IN_EXPRESSION);
            handleExpression(stack, guarded, expression.getChild(1));
            break;

        case DafnyParser.OR:
            child0 = expression.getChild(0);
            handleExpression(stack, current, child0);
            guarded = new SymbexPath(current);
            guarded.addPathCondition(ASTUtil.negate(child0),
                    child0, AssumptionType.GUARD_IN_EXPRESSION);
            handleExpression(stack, guarded, expression.getChild(1));
            break;

        case DafnyParser.ARRAY_ACCESS:
            child0 = expression.getChild(0);
            addNonNullCheck(stack, current, child0);
            addIndexInRangeCheck(stack, current, expression.getChild(1), child0);
            break;

        default:
            for (int i = 0; i < expression.getChildCount(); i++) {
                handleExpression(stack, current, expression.getChild(i));
            }
        }
    }

    private void addIndexInRangeCheck(Deque<SymbexPath> stack, SymbexPath current,
            DafnyTree idx, DafnyTree array) {
        SymbexPath bounds = new SymbexPath(current);
        List<DafnyTree> pos = new ArrayList<>();
        pos.add(ASTUtil.greaterEqual(idx, ASTUtil.intLiteral(0)));
        pos.add(ASTUtil.less(idx, ASTUtil.length(array)));
        bounds.setProofObligations(pos, idx, AssertionType.RT_IN_BOUNDS);
        bounds.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        stack.push(bounds);
    }

    private void addNonNullCheck(Deque<SymbexPath> stack, SymbexPath current,
            DafnyTree expression) {
        SymbexPath nonNull = new SymbexPath(current);
        DafnyTree check = ASTUtil.notEquals(expression, ASTUtil._null());
        nonNull.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        nonNull.setProofObligation(check, expression, AssertionType.RT_NONNULL);
        stack.push(nonNull);
    }
}