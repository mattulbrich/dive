/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ImmutableList;

/**
 * This class captures intermediate and terminal states of paths in symbolic
 * execution.
 *
 * A path for symbolic execution comprises:
 * <ul>
 * <li>a list of gathered path conditions
 * <li>a list of proof obligations to be discharged
 * <li>the kind/nature of the proof obligations (all are of the same kind)
 * <li>the variable assignment under which the obligations are to be examined.
 * <li>the piece of code that remains yet to be examined (empty for terminal
 * states)
 * </ul>
 *
 * A path object is mutable and objects are modified during symbolic execution.
 * At places where more than one state result from symbolic execution, the copy
 * constructor {@link #SymbexState(SymbexPath)} is used.
 *
 * The referred elements are of immutable nature such that they can be shared
 * beween instances of this class.
 *
 * All references to the original code are in form of {@link DafnyTree} AST
 * references.
 */
public class SymbexPath {

    /**
     * The gathered path conditions.
     */
    private ImmutableList<PathConditionElement> pathConditions;

    /**
     * The proof obligations to discharge.
     */
    private ImmutableList<AssertionElement> proofObligations;

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
    public SymbexPath(DafnyTree function) {
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
    public SymbexPath(SymbexPath state) {
        this.pathConditions = state.pathConditions;
        this.proofObligations = state.proofObligations;
        this.currentMap = state.currentMap;
        this.blockToExecute = state.blockToExecute;
        this.function = state.function;
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
        PathConditionElement pathCondition =
                new PathConditionElement(expr, stm, type, currentMap);
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
    public void setProofObligation(DafnyTree obligation, DafnyTree referTo, AssertionType type) {
        assert obligation != null;
        assert type != null;
        AssertionElement element = new AssertionElement(obligation, referTo, type, currentMap);
        this.proofObligations = ImmutableList.single(element);
    }

    public void setProofObligation(AssertionElement proofObl) {
        this.proofObligations = ImmutableList.single(proofObl);
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

    public void setProofObligations(Iterable<DafnyTree> expressions, DafnyTree referTo, AssertionType type) {
        this.proofObligations = ImmutableList.nil();
        for (DafnyTree dafnyTree : expressions) {
            AssertionElement element = new AssertionElement(dafnyTree, referTo, type, currentMap);
            proofObligations = proofObligations.append(element);
        }
    }

    public void setProofObligationsFromLastChild(Iterable<DafnyTree> stms, AssertionType type) {
        this.proofObligations = ImmutableList.nil();
        for (DafnyTree stm : stms) {
            AssertionElement element = new AssertionElement(stm.getLastChild(), stm, type, currentMap);
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
     * Gets the instantiated proof obligations.
     *
     * The result is a list of expression trees.
     *
     * @return a list of proof obligations expressions,
     *  instantiated with the variable map
     */
    @Deprecated
    public List<DafnyTree> getInstantiatedObligationExpressions() {
        List<DafnyTree> result = new ArrayList<>();
        for (AssertionElement po : proofObligations) {
            result.add(currentMap.instantiate(po.getExpression()));
        }
        return result;
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
            switch(type) {
            case IF_ELSE:
            case IF_THEN:
            case WHILE_FALSE:
            case WHILE_TRUE:
                result.append(type.toString()).append("/");
            }
        }

        if(proofObligations.size() > 1) {
            AssertionType type = getCommonProofObligationType();
            if (type != null) {
                result.append("/").append(type);
            }
            result.append("[+]");
        } else if (proofObligations.size() == 0) {
            result.append("[-]");
        } else {
            result.append("/" + proofObligations.get(0));
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
        if(proofObligations.size() == 1) {
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
            if(result == null) {
                result = ass.getType();
            } else if(result != ass.getType()) {
                return null;
            }
        }
        return result;
    }

}