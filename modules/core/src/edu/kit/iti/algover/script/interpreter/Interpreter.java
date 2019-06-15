/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.interpreter;


import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.callhandling.CommandLookup;
//import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.InterpreterRuntimeException;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Visitor;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Main Class for interpreter
 * Interpreter keeps a stack of states
 *
 * @author S.Grebing
 */

// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public class Interpreter<T> extends DefaultASTVisitor<Object>
        implements ScopeObservable {
    private static final int MAX_ITERATIONS = 5;

    /**
     * State stack. Contains the state that is being processed
     */
    private Stack<State<T>> stateStack = new Stack<>();

    /**
     * Listener for entry and exit of ASTNodes
     */
    private List<Visitor<?>> entryListeners = new ArrayList<>(),
            exitListeners = new ArrayList<>();

    /**
     * Matcher for match expressions
     */
    private MatcherApi<T> matcherApi;

    /**
     * Lookup for proof commands
     */
    private CommandLookup functionLookup;

    //Do not remove, it is essential TODO Bugfix
    public void setFunctionLookup(CommandLookup functionLookup) {
        this.functionLookup = functionLookup;
    }

    public Interpreter(CommandLookup lookup) {
        functionLookup = lookup;
    }

    @Override
    public List<Visitor<?>> getEntryListeners() {
        return entryListeners;
    }


    @Override
    public List<Visitor<?>> getExitListeners() {
        return exitListeners;
    }

    public MatcherApi<T> getMatcherApi() {
        return matcherApi;
    }

    public void setMatcherApi(MatcherApi<T> matcherApi) {
        this.matcherApi = matcherApi;
    }

    /**
     * Lookup for call commands/rule applications
     *
     * @return
     */
    public CommandLookup getFunctionLookup() {
        return functionLookup;
    }

    /**
     * Interpret a proof script
     * @param script the parsed proof script AST
     * @throws ScriptCommandNotApplicableException
     * @throws InterpreterRuntimeException
     */
    public void interpret(ProofScript script) throws ScriptCommandNotApplicableException, InterpreterRuntimeException {
        if (stateStack.empty()) {
            throw new InterpreterRuntimeException("No state on stack. call newState before interpret");
        }
        script.accept(this);
    }

    /**
     * Interpret an ASTNode in state on top of stack
     * @param node
     * @throws ScriptCommandNotApplicableException
     * @throws InterpreterRuntimeException
     */
    public void interpret(ASTNode node) throws ScriptCommandNotApplicableException, InterpreterRuntimeException {
        if (stateStack.empty()) {
            throw new InterpreterRuntimeException("no state on stack. call newState before interpret");
        }
        node.accept(this);
    }


    /**
     * Visit a proof script (context is handled by the call of the script noch by visiting the script itself)
     * 1) visit its signature
     * 2) visit its body
     *
     * @param proofScript
     * @return
     */
    @Override
    public Object visit(ProofScript proofScript) {
        enterScope(proofScript);
        //add vars
        visit(proofScript.getSignature());
        proofScript.getBody().accept(this);
        exitScope(proofScript);
        return null;
    }

    /**
     * Visiting an assignment results in changing the variables of the current selected goalnode
     *
     * @param assignmentStatement
     * @return
     */
    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        enterScope(assignmentStatement);

        //ProofNode node = getSelectedNode();
        State<T> currentState = popState();
        ProofNode node = currentState.getSelectedGoalNode();

        ProofNode newNode = new ProofNode(node, null, node.getSequent(), node.getPVC());
        newNode.enterScope();
        newState(newNode);

        Type t = assignmentStatement.getType();
        Variable var = assignmentStatement.getLhs();
        Expression expr = assignmentStatement.getRhs();
        if (t != null) {
            newNode.declareVariable(var, t);
        }

        if (expr != null) {
            Type type = newNode.getVariableType(var);
            if (type == null) {
                throw new RuntimeException("Type of Variable " + var + " is not declared yet");
            } else {
                Value v = evaluate(expr);
                newNode.setVariableValue(var, v);
            }
        }


        //this.getCurrentState().getGoals().remove(node);
        //this.getCurrentState().getGoals().add(newNode);
        //this.getCurrentState().setSelectedGoalNode(newNode);
        exitScope(assignmentStatement);


        return null;
    }


    private Value evaluate(Expression expr) {
        return evaluate(getSelectedNode(), expr);
    }

    /**
     * @param casesStatement
     * @return
     */
    @Override
    public Object visit(CasesStatement casesStatement) {
        enterScope(casesStatement);
        State<T> beforeCases = peekState();

        //List<GoalNode<T>> allGoalsBeforeCases = beforeCases.getGoals();
        List<ProofNode> allGoalsBeforeCases = beforeCases.getGoals();

        //global List after all Case Statements
        List<ProofNode> goalsAfterCases = new ArrayList<>();
        //copy the list of goal nodes for keeping track of goals
        Set<ProofNode> remainingGoalsSet = new HashSet<>(allGoalsBeforeCases);
        //handle cases
        List<CaseStatement> cases = casesStatement.getCases();

//        for (GoalNode<T> goalBeforeCase : allGoalsBeforeCases) {
        for (ProofNode goalBeforeCase : allGoalsBeforeCases) {
            State<T> createdState = newState(goalBeforeCase);//to allow the case to retrieve goal
            boolean result = false;
            for (CaseStatement aCase : cases) {
                result = (boolean) aCase.accept(this);
                if (result) {
                    //remove goal from set for default
                    remainingGoalsSet.remove(goalBeforeCase);
                    //case statement matched and was executed
                    break;
                }
            }
            //remove state from stack
            State<T> stateAfterCase = popState();
            //  System.out.println("State after Case " + stateAfterCase.getSelectedGoalNode().toCellTextForKeYData());
            if (result && stateAfterCase.getGoals() != null) {
                goalsAfterCases.addAll(stateAfterCase.getGoals());
            }


        }

        //===========================================================================================//
       /* for (CaseStatement aCase : cases) {
            if (aCase.isClosedStmt) {
                System.out.println("IsClosableStmt not implemented yet");
            } else {
                Map<GoalNode<T>, VariableAssignment> matchedGoals =
                        matchGoal(remainingGoalsSet, (SimpleCaseStatement) aCase);
                if (matchedGoals != null) {
                    remainingGoalsSet.removeAll(matchedGoals.keySet());
                    goalsAfterCases.addAll(executeCase(aCase.getBody(), matchedGoals));
                }
            }

        }*/

        //for all remaining goals execute default
        if (!remainingGoalsSet.isEmpty()) {
            VariableAssignment va = new VariableAssignment();
            Statements defaultCase = casesStatement.getDefaultCase();
            for (ProofNode goal : remainingGoalsSet) {

                goalsAfterCases.addAll(executeBody(defaultCase, goal, va).getGoals());
            }


        }

        //exit scope and create a new state using the union of all newly created goals

        State<T> newStateAfterCases;
        if (!goalsAfterCases.isEmpty()) {
            //goalsAfterCases.forEach(node -> node.exitScope());
            Stream<ProofNode> goalNodeStream = goalsAfterCases.stream().filter(tGoalNode -> true);
            //!((KeYData) tGoalNode.getData()).getNode().isClosed());
            List<ProofNode> openGoalListAfterCases = goalNodeStream.collect(Collectors.toList());
            /*if (goalsAfterCases.size() == 1) {
                newStateAfterCases = new State<T>(goalsAfterCases, 0);
            } else {
                // newStateAfterCases = new State<T>(goalsAfterCases, null);
            }*/
            if (openGoalListAfterCases.size() == 1) {
                newStateAfterCases = new State<T>(openGoalListAfterCases, 0);
            } else {
                newStateAfterCases = new State<T>(openGoalListAfterCases, null);
            }
            stateStack.push(newStateAfterCases);
        }

        //stateStack.peek().getGoals().removeAll(beforeCases.getGoals());
        exitScope(casesStatement);
        return null;
    }


    /**
     * Visiting a statement list results in visiting each statement
     *
     * @param statements
     * @return
     */
    @Override
    public Void visit(Statements statements) {
        enterScope(statements);
        for (Statement s : statements) {
            s.accept(this);
        }
        exitScope(statements);
        return null;
    }

    /*@Override
    public Object visit(IsClosableCase isClosableCase) {
        State<T> currentStateToMatch = peekState();
        State<T> currentStateToMatchCopy = peekState().copy(); //deepcopy
        GoalNode<T> selectedGoalNode = currentStateToMatch.getSelectedGoalNode();
        GoalNode<T> selectedGoalCopy = currentStateToMatch.getSelectedGoalNode().deepCopy(); //deepcopy

        enterScope(isClosableCase);
        executeBody(isClosableCase.getBody(), selectedGoalNode, new VariableAssignment(selectedGoalNode.getAssignments()));
        State<T> stateafterIsClosable = peekState();
        List<GoalNode<T>> goals = stateafterIsClosable.getGoals();
        boolean allClosed = true;
        for (GoalNode<T> goal : goals) {
            KeyData data = (KeyData) goal.getData();
            if (!data.getNode().isClosed()) {
                allClosed = false;
                break;
            }
        }
        if (!allClosed) {
            System.out.println("IsClosable was not successful, rolling back proof");
            Proof currentKeYproof = ((KeyData) selectedGoalNode.getData()).getProof();
            ImmutableList<Goal> subtreeGoals = currentKeYproof.getSubtreeGoals(((KeyData) selectedGoalNode.getData()).getNode());
            currentKeYproof.pruneProof(((KeyData) selectedGoalCopy.getData()).getNode());
            popState();
            pushState(currentStateToMatchCopy);
        }
        //check if state is closed
        exitScope(isClosableCase);
        return false;
    }*/

    /**
     * Visiting a call statement results in:
     * 0) searching for the handler of the called command
     * 1) saving the context onto the stack and creating a copy of the state and push it onto the stack
     * 2) adding new Variable Assignments to te selected goal
     * 3) adding the assigned parameters to the variable assignments
     * 4) visiting the body respec. letting the handler take over
     * 5) removing the top element form the stack
     *
     * @param call
     * @return
     */
    @Override
    public Object visit(CallStatement call) {
        enterScope(call);
        //neuer VarScope
        //enter new variable scope
        VariableAssignment params = evaluateParameters(call.getParameters());
        ProofNode g = getSelectedNode();
        g.enterScope();
        try {
            functionLookup.callCommand(this, call, params);
        } catch (ScriptCommandNotApplicableException e) {
            System.out.println("Script Command \"" + call.getCommand() + "\" with parameters " + call.getParameters() + " was not applicable on sequent " + g.getSequent());
            throw e;

            /*State<T> newErrorState = newState(null, null);
            newErrorState.setErrorState(true);
            pushState(newErrorState);*/
        }
        g.exitScope();
        exitScope(call);
        return null;
    }

    @Override
    public Object visit(Signature signature) {
        exitScope(signature);
        ProofNode node = getSelectedNode();
        node.enterScope();
        signature.forEach(node::declareVariable);
        enterScope(signature);
        return null;
    }

    @Override
    public Object visit(SimpleCaseStatement simpleCaseStatement) {
        Expression matchExpression = simpleCaseStatement.getGuard();
        State<T> currentStateToMatch = peekState();
        ProofNode selectedGoal = currentStateToMatch.getSelectedGoalNode();

        assert currentStateToMatch.getGoals().contains(selectedGoal);

        VariableAssignment va = evaluateMatchInGoal(matchExpression, selectedGoal);
        if (va != null) {
            enterScope(simpleCaseStatement);
            executeBody(simpleCaseStatement.getBody(), selectedGoal, va);
            //  executeCase(simpleCaseStatement.getBody(), )
            exitScope(simpleCaseStatement);
            return true;
        } else {
            return false;
        }


    }



    /**
     * Evaluate a match in a specific goal
     *
     * @param matchExpression
     * @param goal
     * @return null, if match was false, return the first Assignment when match was true
     */
    private VariableAssignment evaluateMatchInGoal(Expression matchExpression, ProofNode goal) {
        enterScope(matchExpression);
        Evaluator eval = new Evaluator(goal.getAssignments(), goal);

        //System.out.println("Goal to match " + goal);
        MatchEvaluator mEval = new MatchEvaluator(goal, goal.getAssignments(), matcherApi, eval);
        mEval.getEntryListeners().addAll(entryListeners);
        mEval.getExitListeners().addAll(exitListeners);
        List<VariableAssignment> matchResult;
        if (matchExpression.hasMatchExpression()) {
            matchResult = mEval.eval(matchExpression);

        } else {
            matchResult = new ArrayList<>();
            Value eval1 = eval.eval(matchExpression);
            if (eval1.getType().equals(Type.BOOL) && eval1.equals(Value.TRUE)) {
                VariableAssignment emptyAssignment = new VariableAssignment(null);
                matchResult.add(emptyAssignment);
            }

        }
        exitScope(matchExpression);

        if (matchResult.isEmpty()) {
            return null;
        } else {
            return matchResult.get(0);
        }


    }

    private State<T> executeBody(Statements caseStmts, ProofNode goalNode, VariableAssignment va) {
        enterScope(caseStmts);
        goalNode.enterScope(va);
        State<T> s = newState(goalNode);
        caseStmts.accept(this);
        popState();
        exitScope(caseStmts);
        return s;
    }

    //region State Handling
    public ProofNode getSelectedNode() {
        try {
            return stateStack.peek().getSelectedGoalNode();
        } catch (IllegalStateException e) {
            return getCurrentGoals().get(0);
        }
    }

    /**
     * Get goalnodes from current state
     *
     * @return
     */
    public List<ProofNode> getCurrentGoals() {
        return getCurrentState().getGoals();
    }


    public VariableAssignment evaluateParameters(Parameters parameters) {
        VariableAssignment va = new VariableAssignment();
        parameters.entrySet().forEach(entry -> {
            Value val = evaluate(entry.getValue());
            va.declare(entry.getKey(), val.getType());
            va.assign(entry.getKey(), val);
        });
        return va;
    }


    /**
     * Cretae a new state containing only the selected goal node and push to stack
     *
     * @param selected
     * @return reference to state on stack
     */
    public State<T> newState(ProofNode selected) {
        return newState(Collections.singletonList(selected), selected);
    }

    /**
     * Create new state containing goals and selected goal node an push to stack
     *
     * @param goals
     * @param selected
     * @return state that is pushed to stack
     */
    public State<T> newState(List<ProofNode> goals, ProofNode selected) {
        if (selected != null && !goals.contains(selected)) {
            throw new IllegalStateException("selected goal not in list of goals");
        }
        return pushState(new State<>(goals, selected));
    }

    /**
     * Peek current state
     *
     * @return state on top of state stack
     */
    public State<T> getCurrentState() {
        try {
            return stateStack.peek();
        } catch (EmptyStackException e) {
            return new State<T>(null);

        }
    }

    private Value evaluate(ProofNode g, Expression expr) {
        enterScope(expr);
        Evaluator evaluator = new Evaluator(g.getAssignments(), g);
        evaluator.setMatcher(matcherApi);
        evaluator.getEntryListeners().addAll(entryListeners);
        evaluator.getExitListeners().addAll(exitListeners);
        exitScope(expr);
        return evaluator.eval(expr);
    }

    /**
     * Match a set of goal nodes against a matchpattern of a case and return the matched goals together with instantiated variables
     *
     * @param allGoalsBeforeCases
     * @param aCase
     * @return
     */
    private Map<ProofNode, VariableAssignment> matchGoal(Set<ProofNode> allGoalsBeforeCases, SimpleCaseStatement aCase) {

        HashMap<ProofNode, VariableAssignment> matchedGoals = new HashMap<>();
        Expression matchExpression = aCase.getGuard();
        for (ProofNode goal : allGoalsBeforeCases) {
            VariableAssignment va = evaluateMatchInGoal(matchExpression, goal);
            if (va != null) {
                matchedGoals.put(goal, va);
            }
        }
        return matchedGoals;
    }

    /**
     * For each selected goal put a state onto the stack and visit the body of the case
     *
     * @param
     * @param caseStmts
     * @param goalsToApply @return
     */
    private List<ProofNode> executeCase(Statements caseStmts,
                                        Map<ProofNode, VariableAssignment> goalsToApply) {
        enterScope(caseStmts);
        List<ProofNode> goalsAfterCases = new ArrayList<>();

        for (Map.Entry<ProofNode, VariableAssignment> next : goalsToApply.entrySet()) {
            State<T> s = executeBody(caseStmts, next.getKey(), next.getValue());
            goalsAfterCases.addAll(s.getGoals());
        }
        exitScope(caseStmts);
        return goalsAfterCases;


    }

    /**
     * Push state to stack and return reference to this state
     *
     * @param state
     * @return
     */
    public State<T> pushState(State<T> state) {
        if (stateStack.contains(state)) {
            throw new IllegalStateException("State is already on the stack!");
        }
        stateStack.push(state);
        return state;
    }

    /**
     * Remove top level state from stack and throw an Exception if state does not equal expected state
     *
     * @param expected
     * @return
     */
    public State<T> popState(State<T> expected) {
        State<T> actual = stateStack.pop();
        if (!expected.equals(actual)) {
            throw new IllegalStateException("Error on the stack!");
        }
        return actual;
    }

    /**
     * Remove top level state from stack
     *
     * @return
     */
    private State<T> popState() {
        return stateStack.pop();
    }

    /**
     * Lookup state on the stack but do not remove it
     *
     * @return
     */
    public State<T> peekState() {
        return stateStack.peek();
    }

    /**
     * Create a ew state containing the goals but without selected goal node and push to stack
     *
     * @param goals
     * @return
     */
    public State<T> newState(List<ProofNode> goals) {
        return newState(goals, null);
    }


    //endregion
}
