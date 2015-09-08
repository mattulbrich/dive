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


public class Symbex {

    private static final PseudoTree EMPTY_PROGRAM =
            new PseudoTree(new CommonToken(PseudoParser.BLOCK));
    private List<SymbexState> results = new ArrayList<SymbexState>();
    private Deque<SymbexState> stack = new LinkedList<SymbexState>();

    public void symbolicExecution(PseudoTree function) {

        assert function.getType() == PseudoParser.FUNCTION;
        SymbexState initial = makeFromPreconditions(function);

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
                    VariableMap newMap = state.getMap().assign(stm.getChild(0).toString(), stm.getChild(1));
                    state.setMap(newMap);
                    state.setBlockToExecute(remainder);
                    stack.push(state);
                    break;

                case PseudoParser.WHILE:
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
                    state.addPathCondition(new PathConditionElement(neg(guard), stm,
                            AssumptionType.WHILE_FALSE, state.getMap()));
                    state.setBlockToExecute(remainder);
                    results.add(state);
                    break;

                case PseudoParser.IF:
                    PseudoTree cond = stm.getChild(0);
                    PseudoTree then = stm.getChild(1);
                    SymbexState stateElse = new SymbexState(state);
                    state.addPathCondition(new PathConditionElement(cond, stm,
                            AssumptionType.IF_THEN, state.getMap()));
                    state.setBlockToExecute(append(then, remainder));
                    stack.push(state);
                    if(stm.getChildCount() == 3) {
                        stateElse.addPathCondition(new PathConditionElement(neg(cond), stm,
                                AssumptionType.IF_ELSE, state.getMap()));
                        PseudoTree _else = stm.getChild(2);
                        stateElse.setBlockToExecute(append(_else, remainder));
                        stack.push(stateElse);
                    }
                    break;

                case PseudoParser.ASSERT:
                    SymbexState assertedState = new SymbexState(state);
                    assertedState.setBlockToExecute(EMPTY_PROGRAM);
                    assertedState.setProofObligations(stm, AssertionType.ASSERT);
                    results.add(assertedState);
                    state.setBlockToExecute(remainder);
                    stack.add(state);
                    break;

                case PseudoParser.CALL:
                default:
                    throw new UnsupportedOperationException();
                }
            }
        }
    }

    private VariableMap anonymise(VariableMap map, PseudoTree body) {
        Set<String> vars = new HashSet<String>();
        collectAssignedVars(body, vars);
        for (String var : vars) {
            map = map.anonymise(var);
        }
        return map;
    }

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

    private PseudoTree neg(PseudoTree cond) {
        PseudoTree result= new PseudoTree(new CommonToken(PseudoParser.NOT, "not"));
        result.addChild(cond);
        return result;
    }

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

    private PseudoTree makeRemainderTree(PseudoTree block) {

        PseudoTree result= new PseudoTree(new CommonToken(PseudoParser.BLOCK));
        for(int i = 1; i < block.getChildCount(); i++) {
            result.addChild(block.getChild(i));
        }

        return result;
    }

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

    public List<SymbexState> getResults() {
        return results;
    }
}
