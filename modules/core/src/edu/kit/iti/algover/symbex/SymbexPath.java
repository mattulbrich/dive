/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.ImmutableList;
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * This class captures intermediate and terminal states of paths in symbolic
 * execution.
 *
 * A path for symbolic execution comprises:
 * <ul>
 * <li>a list of gathered path conditions
 * <li>a list of proof obligations to be discharged
 * <li>the kind/nature of the proof obligations (all are of the same kind)
 * <li>the history of assignments under which the obligations are to be examined
 * <li>the piece of code that remains yet to be examined (empty for terminal
 * states)
 * </ul>
 *
 * A path object is mutable and objects are modified during symbolic execution.
 * At places where more than one state result from symbolic execution, the copy
 * constructor {@link #SymbexState(SymbexPath)} is used.
 *
 * The referred elements are of immutable nature such that they can be shared
 * between instances of this class.
 *
 * All references to the original code are in form of {@link DafnyTree} AST
 * references.
 *
 * @author mattias ulbrich
 */
public class SymbexPath {

    /**
     * The function to which this symbolic execution state belongs.
     */
    private final @NonNull DafnyTree method;

    /**
     * The gathered path conditions.
     */
    private @NonNull ImmutableList<PathConditionElement> pathConditions;

    /**
     * The proof obligations to discharge.
     */
    private @NonNull ImmutableList<AssertionElement> proofObligations;

    /**
     * The currently active variable assignment map.
     */
    private @NonNull ImmutableList<DafnyTree> assignmentHistory;

    /**
     * The declared local variables up to this point.
     */
    private @NonNull ImmutableList<LocalVarDecl> declaredLocalVars;

    /**
     * The block that remains to be executed. may be an empty block.
     */
    private @NonNull DafnyTree blockToExecute;

    /**
     * The suffix to the path identifier, added to make the identifiers unique.
     */
    private int variantNumber;

    /**
     * Instantiates a new symbolic execution state. It belongs to the given
     * function and is initialised with empty artifacts.
     *
     * @param function
     *            the function to refer to, not <code>null</code>
     */
    public SymbexPath(DafnyTree function) {
        assert function != null;
        this.pathConditions = ImmutableList.nil();
        this.assignmentHistory = ImmutableList.nil();
        this.declaredLocalVars = ImmutableList.nil();
        this.proofObligations = ImmutableList.nil();
        this.blockToExecute = function.getLastChild();
        this.method = function;
    }

    /**
     * Instantiates a new symbolic execution state by copying from another
     * state.
     *
     * @param state
     *            the state to copy, not <code>null</code>
     */
    public SymbexPath(SymbexPath state) {
        this.pathConditions = state.pathConditions;
        this.proofObligations = state.proofObligations;
        this.assignmentHistory = state.assignmentHistory;
        this.blockToExecute = state.blockToExecute;
        this.declaredLocalVars = state.declaredLocalVars;
        this.method = state.method;
    }

    private ImmutableList<LocalVarDecl> initialLocalVars() {
        DafnyTree dummy = new DafnyTree(DafnyParser.VAR, "dummy");
        LocalVarDecl heap = new LocalVarDecl(BuiltinSymbols.HEAP.getName(), ASTUtil.id("Heap"), dummy);
        LocalVarDecl mod = new LocalVarDecl(BuiltinSymbols.MOD.getName(), ASTUtil.id("set<object>"), dummy);
        return ImmutableList.from(heap, mod);
    }

    /**
     * Adds a path condition to this state.
     *
     * @param expr
     *            the expression to be assumed, not <code>null</code>
     * @param stm
     *            the stm from which it arises, not <code>null</code>
     * @param type
     *            the type of the assumption, not <code>null</code>
     */
    public void addPathCondition(DafnyTree expr, DafnyTree stm, AssumptionType type) {
        PathConditionElement pathCondition = new PathConditionElement(expr, stm, type, assignmentHistory);
        pathConditions = pathConditions.append(pathCondition);
    }

    /**
     * Gets the assignment history of this instance.
     *
     * @return the map, not <code>null</code>;
     */
    public ImmutableList<DafnyTree> getAssignmentHistory() {
        return assignmentHistory;
    }

    /**
     * Sets the assignment history of this instance.
     *
     * @param assignmentHistory
     *            the new assignment history, not <code>null</code>
     */
    public void setAssignmentHistory(ImmutableList<DafnyTree> assignmentHistory) {
        this.assignmentHistory = assignmentHistory;
    }

    /**
     * Adds an assignment to the history of this instance.
     *
     * @param assignment
     *            the assignment to add, not <code>null</code>
     */
    public void addAssignment(DafnyTree assignment) {
        assert assignment.getType() == DafnyParser.ASSIGN;
        setAssignmentHistory(assignmentHistory.append(assignment));
    }

    public ImmutableList<LocalVarDecl> getDeclaredLocalVars() {
        return declaredLocalVars;
    }

    public void setDeclaredLocalVars(ImmutableList<LocalVarDecl> declaredLocalVars) {
        this.declaredLocalVars = declaredLocalVars;
    }

    public void addDeclaredLocalVar(LocalVarDecl decl) {
        setDeclaredLocalVars(declaredLocalVars.append(decl));
    }

    /**
     * Gets the function to which this state belongs.
     *
     * @return the function
     */
    // TODO Rename getDeclaration()
    public DafnyTree getMethod() {
        return method;
    }

    /**
     * Gets the block which is yet to be executed.
     *
     * May be an empty AST if a terminal state has been reached.
     *
     * @return the block to execute, not <code>null</code>
     */
    public DafnyTree getBlockToExecute() {
        return blockToExecute;
    }

    /**
     * Sets the block to be executed.
     *
     * During symbolic execution this is updated frequently.
     *
     * @param program
     *            the new block to execute, not <code>null</code>
     */
    public void setBlockToExecute(DafnyTree program) {
        assert program != null;
        this.blockToExecute = program;
    }

    /**
     * Sets a single proof obligations for this state.
     *
     * @param obligation
     *            the single obligation, not <code>null</code>
     * @param type
     *            the type of the obligation, not <code>null</code>
     */
    public void setProofObligation(DafnyTree obligation, DafnyTree referTo, AssertionType type) {
        assert obligation != null;
        assert type != null;
        AssertionElement element = new AssertionElement(obligation, referTo, type);
        this.proofObligations = ImmutableList.single(element);
    }

    public void setProofObligation(AssertionElement proofObl) {
        this.proofObligations = ImmutableList.single(proofObl);
    }

    public void setProofObligations(Iterable<DafnyTree> expressions, DafnyTree referTo, AssertionType type) {
        this.proofObligations = ImmutableList.nil();
        for (DafnyTree dafnyTree : expressions) {
            AssertionElement element = new AssertionElement(dafnyTree, referTo, type);
            proofObligations = proofObligations.append(element);
        }
    }

    public void setProofObligationsFromLastChild(Iterable<DafnyTree> stms, AssertionType type) {
        this.proofObligations = ImmutableList.nil();
        for (DafnyTree stm : stms) {
            AssertionElement element = new AssertionElement(stm.getLastChild(), stm, type);
            proofObligations = proofObligations.append(element);
        }
    }

    /**
     * Gets the set of path conditions.
     *
     * @return the list of path conditions
     */
    public ImmutableList<PathConditionElement> getPathConditions() {
        return pathConditions;
    }

    /**
     * Gets the list of proof obligations.
     *
     * @return the proof obligations
     */
    public ImmutableList<AssertionElement> getProofObligations() {
        return proofObligations;
    }

    /**
     * Sets the set proof obligations for this state. the argument is iterated
     * into a new data structure and may be modified afterwards.
     *
     * @param iterable
     *            the set of obligations
     * @param type
     *            the common type of the obligations, not <code>null</code>.
     */
    public void setProofObligations(Iterable<AssertionElement> iterable) {
        this.proofObligations = ImmutableList.from(iterable);
    }

    /**
     * Gets the unique path identifier which enumerates all decisions made on
     * the path.
     *
     * @return the path identifier
     */
    @SuppressWarnings("incomplete-switch")
    public String getPathIdentifier() {
        StringBuilder result = new StringBuilder();
        for (PathConditionElement pce : pathConditions) {
            AssumptionType type = pce.getType();
            switch (type) {
            case IF_ELSE:
            case IF_THEN:
            case WHILE_FALSE:
            case WHILE_TRUE:
                result.append(type.identifier).append("/");
                break;
            }
        }

        if (proofObligations.size() > 1) {
            AssertionType type = getCommonProofObligationType();
            if (type != null) {
                result.append("/[+").append(type).append("]");
            }
            result.append("[+]");
        } else if (proofObligations.size() == 0) {
            result.append("[-]");
        } else {
            result.append(proofObligations.get(0).getPVCLabelSuffix());
        }

        if (variantNumber != 0) {
            result.append(".").append(variantNumber);
        }

        return result.toString();
    }

    @Override
    public String toString() {
        return getPathIdentifier();
    }

    /**
     * Split a symbex state with more than one proof obligation into several
     * objects.
     *
     * @return a freshly (possibly immutable) list of symbex states.
     */
    public List<SymbexPath> split() {
        if (proofObligations.size() == 1) {
            return Collections.singletonList(this);
        } else {
            List<SymbexPath> result = new ArrayList<>();
            for (AssertionElement proofObl : proofObligations) {
                SymbexPath child = new SymbexPath(this);
                child.setProofObligation(proofObl);
                result.add(child);
            }
            return result;
        }
    }

    public AssertionType getCommonProofObligationType() {
        AssertionType result = null;
        for (AssertionElement ass : proofObligations) {
            if (result == null) {
                result = ass.getType();
            } else if (result != ass.getType()) {
                return null;
            }
        }
        return result;
    }

    /**
     * Increment the {@link #variantNumber} of this path by one.
     *
     * To make identifiers unique, names must be suffixed by number sometimes.
     */
    public void incrementVariant() {
        variantNumber++;
    }

}