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
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.symbex.SymbexState.AssertionType;
import edu.kit.iti.algover.util.ASTUtil;

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
     * The Constant EMPTY_PROGRAM points to an empty AST.
     */
    private static final DafnyTree EMPTY_PROGRAM =
            new DafnyTree(new CommonToken(DafnyParser.BLOCK));

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
    public List<SymbexState> symbolicExecution(DafnyTree function) {

        assert function.getType() == DafnyParser.METHOD;
        SymbexState initial = makeFromPreconditions(function);

        Deque<SymbexState> stack = new LinkedList<SymbexState>();
        List<SymbexState> results = new ArrayList<SymbexState>();

        stack.add(initial);

        while(!stack.isEmpty()) {
            SymbexState state = stack.removeFirst();

            assert state.getBlockToExecute().getType() == DafnyParser.BLOCK;

            if(state.getBlockToExecute().getChildCount() == 0) {
                results.add(state);
            } else {

                DafnyTree stm = state.getBlockToExecute().getChild(0);
                DafnyTree remainder = makeRemainderTree(state.getBlockToExecute());

                switch(stm.getType()) {
                case DafnyParser.ASSIGN:
                    handleAssign(stack, state, stm, remainder);
                    break;

                case DafnyParser.VAR:
                    handleVarDecl(stack, state, stm, remainder);
                    break;

                case DafnyParser.WHILE:
                    handleWhile(stack, results, state, stm, remainder);
                    break;

                case DafnyParser.IF:
                    handleIf(stack, state, stm, remainder);
                    break;

                case DafnyParser.ASSERT:
                    handleAssert(stack, results, state, stm, remainder);
                    break;

                case DafnyParser.ASSUME:
                    handleAssume(stack, state, stm, remainder);
                    break;

                default:
                    throw new UnsupportedOperationException("Unknown code: " + stm.getType());
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
     */
    void handleAssert(Deque<SymbexState> stack,
            List<SymbexState> results, SymbexState state, DafnyTree stm,
            DafnyTree remainder) {
        SymbexState assertedState = new SymbexState(state);
        assertedState.setBlockToExecute(EMPTY_PROGRAM);
        assertedState.setProofObligations(stm, AssertionType.EXPLICIT_ASSERT);
        results.add(assertedState);
        state.setBlockToExecute(remainder);
        // TODO Add asserted condition as assumption
        stack.add(state);
    }

    /**
     * Handle an assume statement
     * This adds a hypothesis to the proof obligation
     * @param stack
     * @param state
     * @param stm
     * @param remainder
     */
    void handleAssume(Deque<SymbexState> stack,
            SymbexState state, DafnyTree stm,
            DafnyTree remainder) {
        SymbexState assumedState = new SymbexState(state);
        assumedState.addPathCondition(new PathConditionElement(stm.getLastChild(),
                stm, AssumptionType.EXPLICIT_ASSUMPTION, state.getMap()));
        assumedState.setBlockToExecute(remainder);
        stack.add(assumedState);
    }

    /*
     * Handle an if statement.
     *
     * Two new states are pushed onto the stack for each branch. Path condition
     * elements are added according to the decision expression.
     */
    void handleIf(Deque<SymbexState> stack, SymbexState state,
            DafnyTree stm, DafnyTree remainder) {
        DafnyTree cond = stm.getChild(0);
        DafnyTree then = stm.getChild(1);
        SymbexState stateElse = new SymbexState(state);
        state.addPathCondition(new PathConditionElement(cond, stm,
                AssumptionType.IF_THEN, state.getMap()));
        state.setBlockToExecute(append(then, remainder));
        stack.push(state);
        stateElse.addPathCondition(new PathConditionElement(ASTUtil.negate(cond), stm,
                AssumptionType.IF_ELSE, state.getMap()));
        if(stm.getChildCount() == 3) {
            DafnyTree _else = stm.getChild(2);
            stateElse.setBlockToExecute(append(_else, remainder));
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
     */
    void handleWhile(Deque<SymbexState> stack,
            List<SymbexState> results, SymbexState state, DafnyTree stm,
            DafnyTree remainder) {
        boolean isLabel = stm.getChild(0).getType() == DafnyParser.LABEL;
        DafnyTree guard = stm.getChild(isLabel ? 1 : 0);
        DafnyTree body = stm.getLastChild();
        List<DafnyTree> invariants = stm.getChildrenWithType(DafnyParser.INVARIANT);

        // 1. initially valid.
        SymbexState invState = new SymbexState(state);
        invState.setBlockToExecute(EMPTY_PROGRAM);
        invState.setProofObligations(invariants, AssertionType.INVARIANT_INITIALLY_VALID);
        results.add(invState);

        // 2. preserves invariant:
        // 2a. assume invariants
        SymbexState preserveState = new SymbexState(state);
        preserveState.setMap(anonymise(preserveState.getMap(), body));
        for (DafnyTree inv : invariants) {
            PathConditionElement pc = new PathConditionElement(inv.getLastChild(), inv,
                    AssumptionType.ASSUMED_INVARIANT, preserveState.getMap());
            preserveState.addPathCondition(pc);
        }
        preserveState.addPathCondition(new PathConditionElement(guard, stm,
                AssumptionType.WHILE_TRUE, state.getMap()));
        preserveState.setBlockToExecute(stm.getLastChild());
        // 2b. show invariants:
        preserveState.setProofObligations(
                invariants,
                AssertionType.INVARIANT_PRESERVED);
        stack.add(preserveState);

        // 3. use case:
        state.setMap(anonymise(state.getMap(), body));
        for (DafnyTree inv : invariants) {
            PathConditionElement pc = new PathConditionElement(inv.getLastChild(), inv,
                    AssumptionType.ASSUMED_INVARIANT, state.getMap());
            state.addPathCondition(pc);
        }
        state.addPathCondition(new PathConditionElement(ASTUtil.negate(guard), stm,
                AssumptionType.WHILE_FALSE, state.getMap()));
        state.setBlockToExecute(remainder);
        stack.add(state);
    }

    /*
     * Handle an assignment.
     *
     * This updates the symbex state and pushes it onto the stack.
     */
    void handleAssign(Deque<SymbexState> stack, SymbexState state,
            DafnyTree stm, DafnyTree remainder) {
        String name = stm.getChild(0).toString();
        DafnyTree expression = stm.getChild(1);
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
     */
    void handleVarDecl(Deque<SymbexState> stack, SymbexState state,
            DafnyTree stm, DafnyTree remainder) {
        if(stm.getChildCount() >= 3) {
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
        case DafnyParser.CALL:
            DafnyTree res = tree.getFirstChildWithType(DafnyParser.RESULTS);
            for (DafnyTree r : res.getChildren()) {
                vars.add(r.toString());
            }
            break;
        default:
            List<DafnyTree> children = tree.getChildren();
            if(children != null) {
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
        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.BLOCK));

        if(prog1.getType() == DafnyParser.BLOCK) {
            for(int i = 0; i < prog1.getChildCount(); i++) {
                result.addChild(prog1.getChild(i));
            }
        } else {
            result.addChild(prog1);
        }

        if(prog2.getType() == DafnyParser.BLOCK) {
            for(int i = 0; i < prog2.getChildCount(); i++) {
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

        DafnyTree result = new DafnyTree(new CommonToken(DafnyParser.BLOCK));
        for(int i = 1; i < block.getChildCount(); i++) {
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
    private SymbexState makeFromPreconditions(DafnyTree function) {
        SymbexState result = new SymbexState(function);

        for(DafnyTree req : function.getChildrenWithType(DafnyParser.REQUIRES)) {
            result.addPathCondition(new PathConditionElement(req.getLastChild(), req,
                    PathConditionElement.AssumptionType.PRE, result.getMap()));
        }

        result.setBlockToExecute(function.getLastChild());
        result.setProofObligations(function.getChildrenWithType(DafnyParser.ENSURES), AssertionType.POST);

        return result;
    }
}
