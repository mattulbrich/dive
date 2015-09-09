package edu.kit.iti.algover;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.PathConditionElement.AssertionType;
import edu.kit.iti.algover.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoTree;
import edu.kit.iti.algover.util.ASTUtil;

/**
 * Symbex can be used to perform symbolic execution on a function.
 *
 * Create an instance and apply {@link #symbolicExecution(PseudoTree)}.
 */
public class Symbex {

    /**
     * The Constant EMPTY_PROGRAM points to an empty AST.
     */
    private static final PseudoTree EMPTY_PROGRAM =
            new PseudoTree(new CommonToken(PseudoParser.BLOCK));

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
    public List<SymbexState> symbolicExecution(PseudoTree function) {

        assert function.getType() == PseudoParser.METHOD;
        SymbexState initial = makeFromPreconditions(function);

        Deque<SymbexState> stack = new LinkedList<SymbexState>();
        List<SymbexState> results = new ArrayList<SymbexState>();

        stack.add(initial);

        while(!stack.isEmpty()) {
            SymbexState state = stack.removeFirst();

            assert state.getBlockToExecute().getType() == PseudoParser.BLOCK;

            if(state.getBlockToExecute().getChildCount() == 0) {
                results.add(state);
            } else {

                PseudoTree stm = state.getBlockToExecute().getChild(0);
                PseudoTree remainder = makeRemainderTree(state.getBlockToExecute());

                switch(stm.getType()) {
                case PseudoParser.ASSIGN:
                    handleAssign(stack, state, stm, remainder);
                    break;

                case PseudoParser.WHILE:
                    handleWhile(stack, results, state, stm, remainder);
                    break;

                case PseudoParser.IF:
                    handleIf(stack, state, stm, remainder);
                    break;

                case PseudoParser.ASSERT:
                    handleAssert(stack, results, state, stm, remainder);
                    break;

                case PseudoParser.CALL:
                default:
                    throw new UnsupportedOperationException();
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
    private void handleAssert(Deque<SymbexState> stack,
            List<SymbexState> results, SymbexState state, PseudoTree stm,
            PseudoTree remainder) {
        SymbexState assertedState = new SymbexState(state);
        assertedState.setBlockToExecute(EMPTY_PROGRAM);
        assertedState.setProofObligations(stm, AssertionType.ASSERT);
        results.add(assertedState);
        state.setBlockToExecute(remainder);
        stack.add(state);
    }

    /*
     * Handle an if statement.
     *
     * Two new states are pushed onto the stack for each branch. Path condition
     * elements are added according to the decision expression.
     */
    private void handleIf(Deque<SymbexState> stack, SymbexState state,
            PseudoTree stm, PseudoTree remainder) {
        PseudoTree cond = stm.getChild(0);
        PseudoTree then = stm.getChild(1);
        SymbexState stateElse = new SymbexState(state);
        state.addPathCondition(new PathConditionElement(cond, stm,
                AssumptionType.IF_THEN, state.getMap()));
        state.setBlockToExecute(append(then, remainder));
        stack.push(state);
        if(stm.getChildCount() == 3) {
            stateElse.addPathCondition(new PathConditionElement(ASTUtil.negate(cond), stm,
                    AssumptionType.IF_ELSE, state.getMap()));
            PseudoTree _else = stm.getChild(2);
            stateElse.setBlockToExecute(append(_else, remainder));
            stack.push(stateElse);
        }
    }

    /*
     * Handle a while statement.
     *
     * Three things happen:
     * 1. a PO for the initial validity is added to the results.
     * 2. a symbex target for the preservation of the invariant is added to the stack
     * 3. a symbex target is added for the continuation of the program after the loop.
     */
    private void handleWhile(Deque<SymbexState> stack,
            List<SymbexState> results, SymbexState state, PseudoTree stm,
            PseudoTree remainder) {
        PseudoTree guard = stm.getChild(0);
        PseudoTree body = stm.getLastChild();
        List<PseudoTree> invariants = stm.getChildrenWithType(PseudoParser.INVARIANT);

        // 1. initially valid.
        SymbexState invState = new SymbexState(state);
        invState.setBlockToExecute(EMPTY_PROGRAM);
        invState.setProofObligations(invariants, AssertionType.INVARIANT_INITIALLY_VALID);
        results.add(invState);

        // 2. preserves invariant:
        // 2a. assume invariants
        SymbexState preserveState = new SymbexState(state);
        preserveState.setMap(anonymise(preserveState.getMap(), body));
        for (PseudoTree inv : invariants) {
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
        for (PseudoTree inv : invariants) {
            PathConditionElement pc = new PathConditionElement(inv.getLastChild(), inv,
                    AssumptionType.ASSUMED_INVARIANT, state.getMap());
            state.addPathCondition(pc);
        }
        state.addPathCondition(new PathConditionElement(ASTUtil.negate(guard), stm,
                AssumptionType.WHILE_FALSE, state.getMap()));
        state.setBlockToExecute(remainder);
        results.add(state);
    }

    /*
     * Handle an assignment.
     *
     * This updates the symbex state and pushes it onto the stack.
     */
    private void handleAssign(Deque<SymbexState> stack, SymbexState state,
            PseudoTree stm, PseudoTree remainder) {
        VariableMap newMap = state.getMap().assign(stm.getChild(0).toString(), stm.getChild(1));
        state.setMap(newMap);
        state.setBlockToExecute(remainder);
        stack.push(state);
    }

    /**
     * Anonymise the bariables which are touched in a loop body.
     *
     * @param map
     *            the initial variable map
     * @param body
     *            the body to analyse
     * @return the updated variable map
     */
    private VariableMap anonymise(VariableMap map, PseudoTree body) {
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
    private void collectAssignedVars(PseudoTree tree, Set<String> vars) {
        switch(tree.getType()) {
        case PseudoParser.ASSIGN:
            vars.add(tree.getChild(0).toString());
            break;
        case PseudoParser.CALL:
            PseudoTree res = tree.getFirstChildWithType(PseudoParser.RESULTS);
            for (PseudoTree r : res.getChildren()) {
                vars.add(r.toString());
            }
            break;
        default:
            List<PseudoTree> children = tree.getChildren();
            if(children != null) {
                for (PseudoTree r : children) {
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
    private PseudoTree append(PseudoTree prog1, PseudoTree prog2) {
        PseudoTree result= new PseudoTree(new CommonToken(PseudoParser.BLOCK));

        if(prog1.getType() == PseudoParser.BLOCK) {
            for(int i = 0; i < prog1.getChildCount(); i++) {
                result.addChild(prog1.getChild(i));
            }
        } else {
            result.addChild(prog1);
        }

        if(prog2.getType() == PseudoParser.BLOCK) {
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
    private PseudoTree makeRemainderTree(PseudoTree block) {

        assert block.getType() == PseudoParser.BLOCK;

        PseudoTree result = new PseudoTree(new CommonToken(PseudoParser.BLOCK));
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
    private SymbexState makeFromPreconditions(PseudoTree function) {
        SymbexState result = new SymbexState(function);

        for(PseudoTree req : function.getChildrenWithType(PseudoParser.REQUIRES)) {
            result.addPathCondition(new PathConditionElement(req.getLastChild(), req,
                    PathConditionElement.AssumptionType.PRE, result.getMap()));
        }

        result.setBlockToExecute(function.getLastChild());
        result.setProofObligations(function.getChildrenWithType(PseudoParser.ENSURES), AssertionType.POST);

        return result;
    }
}
