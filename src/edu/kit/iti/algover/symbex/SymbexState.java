/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofVerificationConditionBuilder;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ImmutableList;

/**
 * This class captures intermediate and terminal states of symbolic execution.
 *
 * A state for symbolic execution comprises:
 * <ul>
 * <li>a list of gathered path conditions
 * <li>a list of proof obligations to be discharged
 * <li>the kind/nature of the proof obligations (all are of the same kind)
 * <li>the variable assignment under which the obligations are to be examined.
 * <li>the piece of code that remains yet to be examined (empty for terminal
 * states)
 * </ul>
 *
 * A state is mutable and objects are modified during symbolic execution. At
 * places where more than one state result from symbolic execution, the copy
 * constructor {@link #SymbexState(SymbexState)} is used.
 *
 * The referred elements are of immutable nature such that they can be shared
 * beween instances of this class.
 *
 * All references to the original code are in form of {@link DafnyTree} AST
 * references.
 */
public class SymbexState {

    /**
     * There are different reasons for assertions.
     */
    public enum AssertionType {
        /**
         * Precondition to be checked prior to method invocation.
         */
        CALL_PRE,

        /**
         * Explicit assertion.
         */
        EXPLICIT_ASSERT,

        /**
         * Implicit assertion (div by zero, null-access, in range, ...)
         */
        IMPLICIT_ASSERT,

        /**
         * Postcondition to be proved.
         */
        POST,

        /**
         * Loop Invariant to be proved inductive.
         */
        INVARIANT_PRESERVED,

        /**
         * Loop Invariant has to hold initially.
         */
        INVARIANT_INITIALLY_VALID;
    }

    /**
     * The gathered path conditions.
     */
    private ImmutableList<PathConditionElement> pathConditions;

    /**
     * The proof obligations to discharge.
     */
    private ImmutableList<DafnyTree> proofObligations;

    /**
     * The type of the proof obligations. One type for all of them.
     *
     * @see #proofObligations
     */
    private AssertionType proofObligationType;

    /**
     * The currently active variable assignment map.
     */
    private VariableMap currentMap;

    /**
     * The block that remains to be executed. may be an empty block.
     */
    private DafnyTree blockToExecute;

    /**
     * The function to which this symbolic execution state belongs.
     */
    private final DafnyTree function;

    /**
     * Instantiates a new symbolic execution state. It belongs to the given
     * function and is initialised with empty artifacts.
     *
     * @param function
     *            the function to refer to, not <code>null</code>
     */
    public SymbexState(DafnyTree function) {
        assert function != null;
        this.pathConditions = ImmutableList.nil();
        this.currentMap = VariableMap.EMPTY;
        this.function = function;
    }

    /**
     * Instantiates a new symbolic execution state by copying from another state.
     *
     * @param state
     *            the state to copy, not <code>null</code>
     */
    public SymbexState(SymbexState state) {
        this.pathConditions = state.pathConditions;
        this.proofObligations = state.proofObligations;
        this.proofObligationType = state.proofObligationType;
        this.currentMap = state.currentMap;
        this.blockToExecute = state.blockToExecute;
        this.function = state.function;
    }

    /**
     * Adds a path condition to this state.
     *
     * @param pathCondition
     *            the path condition to add, not <code>null</code>
     */
    public void addPathCondition(PathConditionElement pathCondition) {
        assert pathCondition != null;
        pathConditions = pathConditions.append(pathCondition);
    }

    /**
     * Gets the variable assignment map of this instance.
     *
     * @return the map, not <code>null</code>;
     */
    public VariableMap getMap() {
        return currentMap;
    }

    /**
     * Sets the variable assignment map.
     *
     * @param newMap
     *            the new map, not <code>null</code>
     */
    public void setMap(VariableMap newMap) {
        assert newMap != null;
        currentMap = newMap;
    }

    /**
     * Gets the function to which this state belongs.
     *
     * @return the function
     */
    public DafnyTree getMethod() {
        return function;
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
    public void setProofObligations(DafnyTree obligation, AssertionType type) {
        assert obligation != null;
        assert type != null;
        this.proofObligations = ImmutableList.single(obligation);
        this.proofObligationType = type;
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
    public void setProofObligations(Iterable<DafnyTree> iterable,
            AssertionType type) {
        this.proofObligations = ImmutableList.from(iterable);
        this.proofObligationType = type;
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
     * Gets the proof obligation type.
     *
     * @return the proof obligation type
     */
    public AssertionType getProofObligationType() {
        return proofObligationType;
    }

    /**
     * Gets the list of proof obligations.
     *
     * @return the proof obligations
     */
    public ImmutableList<DafnyTree> getProofObligations() {
        return proofObligations;
    }

    /**
     * Gets the label for the proof obligation in this object.
     *
     * @return the label, could be <code>null</code>
     */
    private static String getObligationLabel(DafnyTree proofObligation) {
        DafnyTree label = proofObligation.getFirstChildWithType(DafnyParser.LABEL);
        if(label != null) {
            return label.getLastChild().getText();
        }
        return null;
    }

    /**
     * Gets the instantiated proof obligations.
     *
     * The result is a list of expression trees.
     *
     * @return a list of proof obligations expressions,
     *  instantiated with the variable map
     */
    public List<DafnyTree> getInstantiatedObligationExpressions() {
        List<DafnyTree> result = new ArrayList<>();
        for (DafnyTree po : proofObligations) {
            result.add(currentMap.instantiate(po.getLastChild()));
        }
        return result;
    }

    /**
     * Gets the unique path identifier which enumerates all decisions made on
     * the path.
     *
     * @return the path identifier
     */
    public String getPathIdentifier() {
        StringBuilder result = new StringBuilder();
        for (PathConditionElement pce : pathConditions.reverse()) {
            AssumptionType type = pce.getType();
            switch(type) {
            case IF_ELSE:
            case IF_THEN:
            case WHILE_FALSE:
            case WHILE_TRUE:
                result.append(type.toString()).append("/");
            }
        }
        result.append(getProofObligationType());
         if(proofObligations.size() > 1) {
            result.append("[+]");
        } else {
            String label = getObligationLabel(proofObligations.get(0));
            if(label != null) {
                result.append("[" + label + "]");
            }
        }
        return result.toString();
    }

    /**
     * Split a symbex state with more than one proof obligation into several
     * objects.
     *
     * @return a freshly (possibly immutable) list of symbex states.
     */
    public List<SymbexState> split() {
        if(proofObligations.size() == 1) {
            return Collections.singletonList(this);
        } else {
            List<SymbexState> result = new ArrayList<>();
            for (DafnyTree proofObl : proofObligations) {
                SymbexState child = new SymbexState(this);
                child.setProofObligations(proofObl, proofObligationType);
                result.add(child);
            }
            return result;
        }
    }

}