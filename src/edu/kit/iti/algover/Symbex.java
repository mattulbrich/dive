package edu.kit.iti.algover;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.antlr.runtime.CommonToken;

import edu.kit.iti.algover.PathCondition.AssertionType;
import edu.kit.iti.algover.PathCondition.AssumptionType;
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

            assert state.getProgram().getType() == PseudoParser.BLOCK;

            if(state.getProgram().getChildCount() == 0) {
                results.add(state);
            } else {

                PseudoTree stm = state.getProgram().getChild(0);
                PseudoTree remainder = makeRemainderTree(state.getProgram());

                switch(stm.getType()) {
                case PseudoParser.ASSIGN:
                    VariableMap newMap = state.getMap().assign(stm.getChild(0).toString(), stm.getChild(1));
                    state.setMap(newMap);
                    state.setProgram(remainder);
                    stack.push(state);
                    break;

                case PseudoParser.WHILE:
                    PseudoTree guard = stm.getChild(0);
                    PseudoTree body = stm.getLastChild();
                    List<PseudoTree> invariants = stm.getChildrenWithType(PseudoParser.INVARIANT);

                    // 1. initially valid.
                    SymbexState invState = new SymbexState(state);
                    invState.setProgram(EMPTY_PROGRAM);
                    invState.setProofObligations(invariants, AssertionType.ASSERTED_INVARIANT);
                    results.add(invState);

                    // 2. preserves invariant:
                    // 2a. assume invariants
                    SymbexState preserveState = new SymbexState(state);
                    preserveState.setMap(anonymise(preserveState.getMap(), body));
                    for (PseudoTree inv : invariants) {
                        PathCondition pc = new PathCondition(inv, AssumptionType.ASSUMED_INVARIANT, state.getMap());
                        preserveState.addPathCondition(pc);
                    }
                    preserveState.addPathCondition(new PathCondition(guard,
                            AssumptionType.WHILE_TRUE, state.getMap()));
                    preserveState.setProgram(stm.getLastChild());
                    // 2b. show invariants:
                    preserveState.setProofObligations(
                            invariants,
                            AssertionType.ASSERTED_INVARIANT);
                    stack.add(preserveState);

                    // 3. use case:
                    state.setMap(anonymise(preserveState.getMap(), body));
                    state.addPathCondition(new PathCondition(neg(guard),
                            AssumptionType.WHILE_FALSE, state.getMap()));
                    state.setProgram(remainder);
                    state.setProofObligations(invariants, AssertionType.ASSERTED_INVARIANT);
                    results.add(state);
                    break;

                case PseudoParser.IF:
                    PseudoTree cond = stm.getChild(0);
                    PseudoTree then = stm.getChild(1);
                    SymbexState stateElse = new SymbexState(state);
                    state.addPathCondition(new PathCondition(cond, AssumptionType.IF_THEN, state.getMap()));
                    state.setProgram(append(then, remainder));
                    stack.push(state);
                    if(stm.getChildCount() == 3) {
                        stateElse.addPathCondition(new PathCondition(neg(cond), AssumptionType.IF_ELSE, state.getMap()));
                        PseudoTree _else = stm.getChild(2);
                        stateElse.setProgram(append(_else, remainder));
                        stack.push(stateElse);
                    }
                    break;

                case PseudoParser.CALL:
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
        SymbexState result = new SymbexState();

        for(PseudoTree req : function.getChildrenWithType(PseudoParser.REQUIRES)) {
            result.addPathCondition(new PathCondition(req, PathCondition.AssumptionType.PRE, result.getMap()));
        }

        result.setProgram(function.getLastChild());
        result.setProofObligations(function.getChildrenWithType(PseudoParser.ENSURES), AssertionType.POST);

        return result;
    }

    public List<SymbexState> getResults() {
        return results;
    }
}
