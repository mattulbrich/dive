/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Type;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.term.Sequent;

import java.util.*;

/**
 * Class represents one proof node. It has a pointer to its parent node and to the children nodes.
 * If no child node exists, the node is either a leaf in the proof tree or a closed branch
 * (is that a good idea, or should we incorporate a field that is true when node is a closed proof node?)
 * *
 */
public class ProofNode {

    /**
     * The variable assignments for this node
     */
    private VariableAssignment variableAssignments;

    /**
     * Pointer to parent proof node
     */
    private final ProofNode parent;

    /**
     * Proof Rule Application responsible for child
     */
    private final ProofRuleApplication psr;

    // private ProofHistory history;

    /**
     * Pointer to children
     */
    private final List<ProofNode> children = new LinkedList<ProofNode>();;

    /**
     * Root PVC
     */
    private final PVC pvc;

    /**
     * Sequent in this proof node
     */
    private final Sequent sequent;

    /**
     * Is closed node?
     */
    private boolean closed;

    /**
     * Pointer to ASTNode that mutated this node
     */
    private List<ASTNode> mutator;


    public static ProofNode createRoot(PVC pvc) {
        return new ProofNode(null, null, pvc.getSequent(), pvc);
    }

    public ProofNode(ProofNode parent, ProofRuleApplication psr, Sequent seq, PVC rootPVC) {
        this.parent = parent;
        this.psr = psr;
        this.sequent = seq;
        this.pvc = rootPVC;
        this.closed = false;
        this.mutator = new ArrayList<>();
        this.variableAssignments = new VariableAssignment(parent == null ? null : parent.deepCopyAssignments());
    }

    public Sequent getSequent() {
        return sequent;
    }

    public ProofNode getParent() {
        return parent;
    }

    public ProofRuleApplication getPsr() {
        return psr;
    }

    public List<ProofNode> getChildren() {
        return children;
    }

    /**
     * This is essential and needed for proof construction, otherwise the proofnodemanager has no chance to add children
     *
     * @param children
     */
    public void setChildren(List<ProofNode> children) {
        this.children.addAll(children);
    }

    public PVC getPVC() {
        return pvc;
    }

    public boolean isClosed() {
        return closed;
    }

    public void setClosed(boolean closed) {
        assert !closed || children.isEmpty() : "Only empty nodes can be closed";
        this.closed = closed;
    }

    /**
     * Returns true if there is no leaf in the tree beneath that is an open goal
     *
     * @return true if the spanned subtree is closed.
     */
    public boolean allLeavesClosed() {
        return isClosed() ||
                (!getChildren().isEmpty()
                        && getChildren().stream().allMatch(ProofNode::allLeavesClosed));
    }

    public void addMutator(ASTNode mutator) {
        this.mutator.add(mutator);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        if (this.getParent() == null) {
            sb.append("Root Node:\n");
        } else {
            sb.append("Proof Node:\n");
        }

        if (!this.variableAssignments.isEmpty()) {
            //sb.append("Variable Assignments");
            sb.append(variableAssignments.toString());
        } else {
            sb.append("Empty Assignments");
        }
        sb.append("Sequent:\n" + this.sequent.toString() + "\n");
        sb.append("\nMutator for this Node: ");
        if (!mutator.isEmpty()) {
            sb.append("\nMutator-Type: " + mutator.get(0).getNodeName());

            sb.append("\n" + mutator.get(0).getRuleContext().getText());
            if (mutator.size() != 1)
                sb.append("\nNumber of Mutators: " + mutator.size());
        }

        return sb.toString();
    }

    public List<ASTNode> getMutator() {
        return mutator;
    }

    private void setMutator(List<ASTNode> mutator) {
        this.mutator = mutator;
    }

    private VariableAssignment deepCopyAssignments() {
        return this.variableAssignments.deepCopy();
    }

    /****************************************************************************************************************
     *
     *                                          Section  for Handling VariableAssignments
     *
     ****************************************************************************************************************/

    public VariableAssignment getVariableAssignments() {
        return variableAssignments;
    }

    public void setVariableAssignments(VariableAssignment variableAssignments) {
        this.variableAssignments = variableAssignments;
    }

    /**
     * @param varname
     * @return value of variable if it exists
     */
    public Value getVariableValue(Variable varname) {
        return variableAssignments.getValue(varname);

    }

    /**
     * Lookup the type of the variable in the type map
     *
     * @param varname
     * @return
     */
    public Type getVariableType(Variable varname) {
        Type t = this.getAssignments().getType(varname);
        if (t == null) {
            throw new RuntimeException("Variable " + varname + " must be declared first");
        } else {

            return t;
        }
    }

    public VariableAssignment getAssignments() {
        return this.variableAssignments;
    }

    /**
     * Add a variable declaration to the type map (TODO Default value in map?)
     *
     * @param name
     * @param type
     * @throws NullPointerException
     */
    public void declareVariable(Variable name, Type type) {
        this.getAssignments().declare(name, type);
    }

    /**
     * Set the value of a variable in the value map
     *
     * @param name
     * @param value
     */
    public void setVariableValue(Variable name, Value value) {
        getAssignments().assign(name, value);
    }

    /**
     * Enter new variable scope and push onto stack
     */
    public VariableAssignment enterScope() {
        variableAssignments = variableAssignments.push();
        return variableAssignments;
    }


    public VariableAssignment exitScope() {
        this.variableAssignments = this.variableAssignments.pop();
        return variableAssignments;
    }

    public VariableAssignment enterScope(VariableAssignment va) {
        variableAssignments = variableAssignments.push(va);
        return variableAssignments;
    }
}
