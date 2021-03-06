/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.TarjansAlgorithm;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ModifiesListResolver;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

import java.util.*;

/**
 * Symbex can be used to perform symbolic execution on a function.
 *
 * Create an instance and apply {@link #symbolicExecution(DafnyTree)}.
 *
 * It produces a list of {@link SymbexPath}s which contain assertions to show
 * and assumptions to be assumed for this path.
 *
 * The handle-methods are package visible to allow for testing from within
 * the package.
 */
public class Symbex {

    /**
     * This dummy node is used to indicate that the heap variable has been
     * assigned to.
     */
    public static final DafnyTree HEAP_VAR = new DafnyTree(DafnyParser.VAR, "heap");

    /**
     * The designated variable that represents decreases clauses.
     */
    public static final String DECREASES_VAR = "$decr";

    /**
     * The Constant EMPTY_PROGRAM points to an empty AST.
     */
    public static final DafnyTree EMPTY_PROGRAM =
            new DafnyTree(DafnyParser.BLOCK);

    /**
     * Performs symbolic execution on a method.
     *
     * It returns all proof obligations which arise during this execution. At
     * the moment, the process is neither scriptable nor configurable.
     *
     * @param method
     *            the method to execute, not <code>null</code>
     * @return a freshly created list of symbolic execution states, not
     *         <code>null</code>
     */
    public List<SymbexPath> symbolicExecution(DafnyTree method) {

        assert method != null;
        assert method.getType() == DafnyParser.METHOD;
        SymbexPath initial = makeFromPreconditions(method);

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

                switch (stm.getType()) {
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

                case DafnyParser.CALL:
                    handleCallStatement(stack, state, stm, remainder);
                    break;

                case DafnyParser.PRINT:
                    // TODO just ignore it for now ... RT tests for arguments ...
                    state.setBlockToExecute(remainder);
                    stack.add(state);
                    break;

                case DafnyParser.RETURN:
                    handleReturnStatement(stack, state, method);
                    break;

                default:
                    throw new UnsupportedOperationException("Unsupported statement: "
                                + DafnyParser.tokenNames[stm.getType()]);
                }
            }
        }

        return results;
    }

    private void handleCallStatement(Deque<SymbexPath> stack, SymbexPath state, DafnyTree stm, DafnyTree remainder) {

        DafnyTree receiver;
        DafnyTree method = stm.getChild(0).getDeclarationReference();
        DafnyTree args = stm.getLastChild();

        if(stm.getChildCount() > 2) {
            receiver = stm.getChild(1);
        } else {
            receiver = null;
        }

        SymbexPath newState = new SymbexPath(state);
        handleMethodCall(stack, newState, stm, receiver, true, method, args);
        newState.setBlockToExecute(remainder);
        stack.add(newState);
    }

    /**
     * Handle a call statement
     *
     * var $resultN : R;
     * assert pre_m;
     * assert variant_m < my_variant   (if appropriate)
     * $heap := anon($heap, mod, anonheap);
     * assume post_m;
     * assume isCreated($resultN) (if appropriate)
     *
     *
     * @returns a DafnyTree which can be used to access
     * the result of the call for later use.
     */
    private List<DafnyTree> handleMethodCall(Deque<SymbexPath> stack, SymbexPath state,
                                       DafnyTree refersTo,
                                       DafnyTree receiver, boolean nullCheckReceiver,
                                       DafnyTree method, DafnyTree args) {

        assert method.getType() == DafnyParser.METHOD;

        String methodname = method.getChild(0).getText();
        List<Pair<String, DafnyTree>> subs = new ArrayList<>();

        // bring up result value
        DafnyTree returns = method.getFirstChildWithType(DafnyParser.RETURNS);
        List<DafnyTree> result = new ArrayList<>();
        if(returns != null) {
            for (DafnyTree ret : returns.getChildren()) {
                DafnyTree type = ret.getFirstChildWithType(DafnyParser.TYPE).getChild(0);
                DafnyTree newVar = ASTUtil.freshVariable("$res_" + methodname, type, state);
                result.add(newVar);
                subs.add(new Pair<>(ret.getChild(0).getText(), newVar));
            }
        }

        // Receiver must be mapped to "this"
        if(receiver != null) {
            subs.add(new Pair<>("this", receiver));
        }

        subs.addAll(ASTUtil.methodParameterSubs(method, args));

        // Preconditions satisfied
        for (DafnyTree req : method.getChildrenWithType(DafnyParser.REQUIRES)) {
            SymbexPath reqState = new SymbexPath(state);
            reqState.setBlockToExecute(EMPTY_PROGRAM);
            DafnyTree condition = req.getLastChild();
            // wrap that into a substitution
            condition = ASTUtil.letCascade(subs, condition);
            reqState.setProofObligation(condition, refersTo, AssertionType.CALL_PRE);
            stack.add(reqState);
        }

        // variant if in recursion loop.
        DafnyTree callerSCC = state.getMethod().getExpressionType();
        DafnyTree calleeSCC = method.getExpressionType();
        assert callerSCC.getType() == TarjansAlgorithm.CALLGRAPH_SCC
            && calleeSCC.getType() == TarjansAlgorithm.CALLGRAPH_SCC;
        if(callerSCC.getText().equals(calleeSCC.getText())) {
            // both in same stron. conn. component ==> potential cycle
            DafnyTree decr = method.getFirstChildWithType(DafnyParser.DECREASES);
            if(decr == null) {
                decr = ASTUtil.intLiteral(0);
                // TODO rather throw an exception?
            } else {
                decr = decr.getLastChild();
            }
            decr = ASTUtil.letCascade(subs, decr);
            DafnyTree condition = ASTUtil.noetherLess(
                    ASTUtil.create(DafnyParser.LISTEX, decr),
                    ASTUtil.create(DafnyParser.LISTEX, ASTUtil.id("$decr")));
            // wrap that into a substitution
            condition = ASTUtil.letCascade(subs, condition);
            SymbexPath decrState = new SymbexPath(state);
            decrState.setBlockToExecute(EMPTY_PROGRAM);
            decrState.setProofObligation(condition, refersTo, AssertionType.VARIANT_DECREASED);
            stack.add(decrState);
        }

        // Modify heap if not strictly pure
        // Ensure modified set is in local modifies.
        if(!ProgramDatabase.isStrictlyPure(method)) {
            DafnyTree mod = method.getFirstChildWithType(DafnyParser.MODIFIES);

            try {
                if (mod == null) {
                    mod = ASTUtil.create(DafnyParser.MODIFIES);
                }
                mod = ModifiesListResolver.resolve(mod);
                mod = ASTUtil.letCascade(subs, mod);
            } catch (DafnyException ex) {
                // We assume that this never occurs in reality
                // TypeResolver checks the typing and fails way earlier!
                throw new RuntimeException(ex);
            }

            // "assert mod_of_method <= $mod"
            SymbexPath modState = new SymbexPath(state);
            modState.setBlockToExecute(EMPTY_PROGRAM);
            DafnyTree condition = ASTUtil.create(DafnyParser.LE,
                    mod.dupTree(), ASTUtil.builtInVar("$mod"));
            modState.setProofObligation(condition, refersTo, AssertionType.MODIFIES);
            stack.add(modState);

            // "heap := anon(heap, mod, ...)"
            state.addAssignment(ASTUtil.anonymiseHeap(state, mod));

            // if result is reference type: it is created
            if(returns != null) {
                List<DafnyTree> allFresh = new ArrayList<>();
                for (DafnyTree ret : returns.getChildren()) {
                    DafnyTree type = ret.getFirstChildWithType(DafnyParser.TYPE).getChild(0);
                    Sort sort = ASTUtil.toSort(type);
                    if(sort.isReferenceSort()) {
                        DafnyTree fresh = ASTUtil.call("$isCreated",
                                ASTUtil.builtInVar("$heap"), ret.getChild(0));
                        allFresh.add(fresh);
                    }
                }
                if (!allFresh.isEmpty()) {
                    DafnyTree cond = ASTUtil.and(allFresh);
                    cond = ASTUtil.letCascade(subs, cond);
                    state.addPathCondition(cond, refersTo, AssumptionType.IMPLICIT_ASSUMPTION);
                }
            }

        }

        // now assume the postcondition (and some free postconditions)
        for (DafnyTree ens : method.getChildrenWithType(DafnyParser.ENSURES)) {
            DafnyTree condition = ens.getLastChild();
            condition = ASTUtil.letCascade(subs, condition);
            state.addPathCondition(condition, refersTo, AssumptionType.CALL_POST);
        }

        return result;
    }

    /*
     * handle "new C;" (possible "new C.method()")
     * as well as "new int[10]"
     */

    private DafnyTree handleNewCommand(Deque<SymbexPath> stack, SymbexPath current, DafnyTree newExpr, DafnyTree stm) {
        switch (newExpr.getChild(0).getType()) {
        case DafnyParser.ARRAY_ACCESS:
            return handleNewArray(stack, current, newExpr, stm);
        case DafnyParser.ID:
            return handleNewClass(stack, current, newExpr, stm);
        default:
            throw new Error("Unexpected 'new' command: " + stm);
        }
    }
    /*
     * new type[size] becomes
     *
     * assert runtime assertions for "size";
     * var $newN : array<type>;
     * assume !isCreated($heap, $newN);
     * $heap := create($heap, $newN);
     * assume $newN.Length == size;
     */

    private DafnyTree handleNewArray(Deque<SymbexPath> stack, SymbexPath current, DafnyTree newExpr, DafnyTree stm) {
        assert newExpr.getType() == DafnyParser.NEW;

        DafnyTree child = newExpr.getChild(0);
        assert child.getType() == DafnyParser.ARRAY_ACCESS;

        DafnyTree type = child.getChild(0);
        DafnyTree size = child.getChild(1);
        DafnyTree arrayType = ASTUtil.create(DafnyParser.ARRAY, "array", type);

        SymbexExpressionValidator.handleExpression(stack, current, size);
        addGreater0Check(stack, current, size);

        DafnyTree newObj = ASTUtil.freshVariable("$new", arrayType, current);
        current.addPathCondition(ASTUtil.negate(ASTUtil.builtIn(ASTUtil.call("$isCreated", ASTUtil.builtInVar("$heap"), newObj))), stm,
                AssumptionType.IMPLICIT_ASSUMPTION);
        current.addAssignment(ASTUtil.assign(ASTUtil.builtIn(ASTUtil.id("$heap")),
                ASTUtil.builtIn(ASTUtil.call("$create", ASTUtil.builtInVar("$heap"), newObj.dupTree()))));
        current.addPathCondition(ASTUtil.equals(ASTUtil.length(newObj), size), stm,
                AssumptionType.IMPLICIT_ASSUMPTION);

        return newObj;
    }

    private void addGreater0Check(Deque<SymbexPath> stack, SymbexPath current,
                                 DafnyTree size) {
        SymbexPath bounds = new SymbexPath(current);
        List<DafnyTree> pos = new ArrayList<>();
        pos.add(ASTUtil.greaterEqual(size, ASTUtil.intLiteral(0)));
        bounds.setProofObligations(pos, size, AssertionType.RT_IN_BOUNDS);
        bounds.setBlockToExecute(Symbex.EMPTY_PROGRAM);
        stack.push(bounds);
    }


    /*
     * new C.Init(p) becomes
     *
     * var $newN : C;
     * assume !isCreated($heap, $newN);
     * $heap := create($heap, $newN);
     *
     * there may be more if a constructor method is mentioned.
     *
     */

    private DafnyTree handleNewClass(Deque<SymbexPath> stack, SymbexPath current, DafnyTree newExpr, DafnyTree stm) {

        assert newExpr.getType() == DafnyParser.NEW;

        DafnyTree clss = newExpr.getChild(0);
        assert clss.getType() == DafnyParser.ID;

        DafnyTree newObj = ASTUtil.freshVariable("$new", clss, current);

        current.addPathCondition(ASTUtil.negate(ASTUtil.builtIn(ASTUtil.call("$isCreated", ASTUtil.builtInVar("$heap"), newObj))), stm,
                AssumptionType.IMPLICIT_ASSUMPTION);
        current.addAssignment(ASTUtil.assign(ASTUtil.builtIn(ASTUtil.id("$heap")),
                ASTUtil.builtIn(ASTUtil.call("$create", ASTUtil.builtInVar("$heap"), newObj.dupTree()))));

        if (newExpr.getChildCount() > 1) {
            DafnyTree call = newExpr.getChild(1);
            DafnyTree method = call.getChild(0).getDeclarationReference();
            DafnyTree args = call.getChild(1);
            handleMethodCall(stack, current, call, newObj, false, method, args);
        }

        return newObj;
    }

    private void handleReturnStatement(Deque<SymbexPath> stack, SymbexPath state, DafnyTree method) {

        // No more code
        state.setBlockToExecute(EMPTY_PROGRAM);

        state.setProofObligationsFromLastChild(
                method.getChildrenWithType(DafnyParser.ENSURES),
                AssertionType.POST);

        stack.add(state);
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
        SymbexExpressionValidator.handleExpression(stack, state, cond);

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
        List<DafnyTree> invariants = stm.getChildrenWithType(DafnyParser.INVARIANT);

        // 1. initially valid.
        SymbexPath invState = new SymbexPath(state);
        invState.setBlockToExecute(EMPTY_PROGRAM);
        invState.setProofObligationsFromLastChild(invariants,
                AssertionType.INVARIANT_INITIALLY_VALID);
        stack.add(invState);

        // 2. preserves invariant:
        // 2a. assume invariants
        SymbexPath preservePath = new SymbexPath(state);
        anonymise(preservePath, body);
        List<DafnyTree> decreaseVars = introduceDecreasesVars(stm, decreasesClause, preservePath);
        for (DafnyTree inv : invariants) {
            preservePath.addPathCondition(inv.getLastChild(), inv,
                    AssumptionType.ASSUMED_INVARIANT);
        }

        // guard well-def
        SymbexExpressionValidator.handleExpression(stack, preservePath, guard);

        preservePath.addPathCondition(guard, stm, AssumptionType.WHILE_TRUE);
        preservePath.setBlockToExecute(stm.getLastChild());

        // 2b. show invariants:
        preservePath.setProofObligationsFromLastChild(invariants,
                AssertionType.INVARIANT_PRESERVED);

        // 2c. show decreases clause:

        AssertionElement decrProof;
        if (decreasesClause != null) {
            DafnyTree decrReduced = ASTUtil.noetherLess(
                    ASTUtil.listExpr(decreasesClause.getChildren()),
                    ASTUtil.listExpr(decreaseVars));
            decrProof = new AssertionElement(decrReduced, decreasesClause,
                    AssertionType.VARIANT_DECREASED);
        } else {
            // no decreases clause specified ... fail!
            decrProof = new AssertionElement(ASTUtil._false(), stm,
                    AssertionType.VARIANT_DECREASED);
        }

        ImmutableList<AssertionElement> oldPOs = preservePath.getProofObligations();
        preservePath.setProofObligations(oldPOs.append(decrProof));
        stack.add(preservePath);

        // 3. use case:
        anonymise(state, body);
        for (DafnyTree inv : invariants) {
            state.addPathCondition(inv.getLastChild(), inv, AssumptionType.ASSUMED_INVARIANT);
        }
        state.addPathCondition(ASTUtil.negate(guard), stm, AssumptionType.WHILE_FALSE);
        state.setBlockToExecute(remainder);
        stack.add(state);
    }

    private List<DafnyTree> introduceDecreasesVars(DafnyTree stm, DafnyTree decreases, SymbexPath preservePath) {

        List<DafnyTree> result = new ArrayList<>();
        if (decreases != null) {
            for (DafnyTree dec : decreases.getChildren()) {
                DafnyTree decreaseVar = makeDecreaseVar(preservePath, stm);
                preservePath.addAssignment(ASTUtil.assign(decreaseVar, dec));
                result.add(decreaseVar);
            }
        }
        return result;
    }

    /*
     * Find the first decreases variable which has not been assigned to.
     *
     * Add it to the declarations list and return its name.
     */
    private DafnyTree makeDecreaseVar(SymbexPath path, DafnyTree stm) {

        // TODO go beyond integer here ...
        DafnyTree intType = new DafnyTree(DafnyParser.INT, "int");
        DafnyTree result = ASTUtil.freshVariable(DECREASES_VAR, intType, path);

        return result;
    }

    /*
     * Handle an assignment.
     *
     * This updates the symbex state and pushes it onto the stack.
     *
     * The history of assignments is updated
     *
     * Checkstyle: IGNORE JavadocMethod
     */
    void handleAssign(Deque<SymbexPath> stack, SymbexPath state,
            DafnyTree stm, DafnyTree remainder) {
        
        if(stm.getChildCount() > 2) {
            // multi-return method invocation like "x,y := meth();" 
            handleMultiReturnAssign(stack, state, stm, remainder);
            return;
        }
        
        DafnyTree assignee = stm.getChild(0);
        SymbexExpressionValidator.handleExpression(stack, state, assignee);
        addModifiesCheck(stack, state, assignee);

        DafnyTree expression = stm.getChild(1);
        switch(expression.getType()) {
        case DafnyParser.CALL:
            DafnyTree decl = expression.getChild(expression.getChildCount()-2).getDeclarationReference();
            if(decl.getType() == DafnyParser.METHOD) {
                DafnyTree receiver = expression.getChildCount() > 2 ? expression.getChild(1) : null;
                DafnyTree args = expression.getFirstChildWithType(DafnyParser.ARGS);
                List<DafnyTree> resultVars = handleMethodCall(stack, state, expression, receiver, true, decl, args);
                assert resultVars.size() == 1 : "This is a single result method situation";
                DafnyTree assignment = ASTUtil.assign(assignee, resultVars.get(0));
                assignment.copyTokensFrom(stm);
                state.addAssignment(assignment);
            } else {
                SymbexExpressionValidator.handleExpression(stack, state, expression);
                state.addAssignment(stm);
            }
            break;

        case DafnyParser.NEW:
            DafnyTree newVar = handleNewCommand(stack, state, expression, stm);
            DafnyTree assignment = ASTUtil.assign(assignee, newVar);
            assignment.copyTokensFrom(stm);
            state.addAssignment(assignment);
            break;

        default:
            SymbexExpressionValidator.handleExpression(stack, state, expression);
            state.addAssignment(stm);
            break;
        }

        state.setBlockToExecute(remainder);
        stack.push(state);
    }

    private void handleMultiReturnAssign(Deque<SymbexPath> stack, SymbexPath state, DafnyTree stm, DafnyTree remainder) {
        DafnyTree expression = stm.getLastChild();
        assert expression.getType() == DafnyParser.CALL : "Should be prevented by parser";

        for (int i = 0; i < stm.getChildCount() - 1; i++) {
            DafnyTree assignee = stm.getChild(i);
            SymbexExpressionValidator.handleExpression(stack, state, assignee);
            addModifiesCheck(stack, state, assignee);
        }

        DafnyTree decl = expression.getChild(expression.getChildCount()-2).getDeclarationReference();
        assert decl.getType() == DafnyParser.METHOD : "Should be prevented by reference resolution";

        DafnyTree receiver = expression.getChildCount() > 2 ? expression.getChild(1) : null;
        DafnyTree args = expression.getFirstChildWithType(DafnyParser.ARGS);
        List<DafnyTree> resultVars = handleMethodCall(stack, state, expression, receiver, true, decl, args);

        int no = 0;
        for (DafnyTree resultVar : resultVars) {
            state.addAssignment(ASTUtil.assign(stm.getChild(no++), resultVar));
        }

        state.setBlockToExecute(remainder);
        stack.push(state);
    }


    private void addModifiesCheck(Deque<SymbexPath> stack, SymbexPath current,
                                  DafnyTree receiver) {
        switch(receiver.getType()) {
        case DafnyParser.ARRAY_ACCESS:
            DafnyTree type = receiver.getChild(0).getExpressionType();
            Sort sort = ASTUtil.toSort(type);
            if(!(sort.isClassSort() || sort.isArray())) {
                // Assigning a sequence/map/... is not relevant
                return;
            }
            // fall through intended!

        case DafnyParser.FIELD_ACCESS:
            SymbexPath nonNull = new SymbexPath(current);
            // the first argument is the modified object
            DafnyTree object = receiver.getChild(0);
            if(object.getType() == DafnyParser.THIS) {
                // no modifies check for the this object!
                return;
            }
            DafnyTree check = ASTUtil.inMod(object);
            nonNull.setBlockToExecute(Symbex.EMPTY_PROGRAM);
            nonNull.setProofObligation(check, check, AssertionType.MODIFIES);
            stack.push(nonNull);
        }
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
        DafnyTree last = stm.getLastChild();
        if(last.getType() == DafnyParser.TYPE) {
            state.setBlockToExecute(remainder);
            stack.push(state);
        } else {
            DafnyTree id = stm.getChild(0);
            DafnyTree expression = last;
            DafnyTree assign = ASTUtil.assign(id, expression);
            assign.getChild(0).setDeclarationReference(stm);
            // defer to assignment handling in this case
            handleAssign(stack, state, assign, remainder);
        }
    }

    /**
     * Anonymise the variables which are touched in a loop body.
     *
     * @param path
     *            the initial variable map
     * @param body
     *            the body to analyse
     * @return the updated variable map
     */
    private void anonymise(SymbexPath path, DafnyTree body) {
        Set<DafnyTree> vars = new LinkedHashSet<>();
        collectAssignedVars(body, vars);
        for (DafnyTree var : vars) {
            if (var != HEAP_VAR) {
                path.addAssignment(ASTUtil.anonymise(var));
            }
        }
        if (vars.contains(HEAP_VAR)) {
            path.addAssignment(ASTUtil.anonymiseHeap(path));
        }
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
    private void collectAssignedVars(DafnyTree tree, Set<DafnyTree> vars) {
        switch (tree.getType()) {
        case DafnyParser.ASSIGN:
            DafnyTree receiver = tree.getChild(0);
            switch (receiver.getType()) {
            case DafnyParser.ID:
                switch (receiver.getDeclarationReference().getType()) {
                    case DafnyParser.VAR:
                        vars.add(receiver.getDeclarationReference());
                        break;
                    case DafnyParser.FIELD:
                        vars.add(HEAP_VAR);
                        break;
                    default:
                        throw new Error(tree.toString());
                }
                break;

            case DafnyParser.ARRAY_ACCESS:
                DafnyTree arrayLike = receiver.getChild(0);
                if(arrayLike.getExpressionType().getType() == DafnyParser.SEQ &&
                      arrayLike.getDeclarationReference().getType() == DafnyParser.VAR) {
                    vars.add(arrayLike.getDeclarationReference());
                } else {
                    vars.add(HEAP_VAR);
                }
                break;

            case DafnyParser.FIELD_ACCESS:
                vars.add(HEAP_VAR);
                break;

            default: throw new Error("Unsupported assignment target: " + tree.toString());
            }
            break;

        case DafnyParser.CALL:
            // TODO ... is this index right?
            DafnyTree callee = tree.getChild(0);
            DafnyTree declRef = callee.getDeclarationReference();
            if (declRef.getType() == DafnyParser.METHOD) {
                // TODO Add check if method is strictly pure.
                vars.add(HEAP_VAR);
            }
            break;
        }

        List<DafnyTree> children = tree.getChildren();
        if (children != null) {
            for (DafnyTree r : children) {
                collectAssignedVars(r, vars);
            }
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
     * Add assignment to modifies variable.
     *
     * @param method
     *            the method to analyse
     * @return the initial symbolic execution state
     */
    private SymbexPath makeFromPreconditions(DafnyTree method) {
        SymbexPath result = new SymbexPath(method);

        for (DafnyTree req : method.getChildrenWithType(DafnyParser.REQUIRES)) {
            result.addPathCondition(req.getLastChild(), req, AssumptionType.PRE);
        }

        result.setProofObligationsFromLastChild(
                method.getChildrenWithType(DafnyParser.ENSURES),
                AssertionType.POST);

        DafnyTree modifies = method.getFirstChildWithType(DafnyParser.MODIFIES);
        if (modifies == null) {
            modifies = ASTUtil.create(DafnyParser.MODIFIES);
        }

        try {
            DafnyTree mod = ModifiesListResolver.resolve(modifies);
            DafnyTree freshObj = ASTUtil.call(BuiltinSymbols.FRESH_OBJECTS.getName(),
                    ASTUtil.id(BuiltinSymbols.HEAP.getName()));
            if (mod.getType() == DafnyParser.SETEX && mod.getChildCount() == 0) {
                mod = freshObj;
            } else {
                mod = ASTUtil.plus(mod, freshObj);
            }

            result.addAssignment(ASTUtil.assign(ASTUtil.builtInVar("$mod"), mod));
        } catch (DafnyException e) {
            // Thanks to TypeResolver, this should never occur.
            throw new RuntimeException(e);
        }

        DafnyTree decreases = method.getFirstChildWithType(DafnyParser.DECREASES);
        if(decreases == null) {
            result.addAssignment(ASTUtil.assign(ASTUtil.builtInVar("$decr"),
                    ASTUtil.intLiteral(0)));
        } else {
            result.addAssignment(ASTUtil.assign(ASTUtil.builtInVar("$decr"),
                    decreases.getLastChild()));
        }

        // $oldheap := $heap ... to remember for old-expressions
        result.addAssignment(ASTUtil.assign(ASTUtil.builtInVar("$oldheap"),
                    ASTUtil.builtInVar("$heap")));

        return result;
    }


}
