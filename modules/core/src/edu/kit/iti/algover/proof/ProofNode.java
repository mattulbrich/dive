/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.term.Sequent;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.*;

/**
 * Class represents one proof node. It has a pointer to its parent node and to the children nodes.
 * If no child node exists, the node is either a leaf in the proof tree or a closed branch
 * (is that a good idea, or should we incorporate a field that is true when node is a closed proof node?)
 *
 * @author Sarah Grebing, Mattias Ulbrich
 */

public class ProofNode {

    /**
     * Pointer to parent proof node
     */
    private final ProofNode parent;

    /**
     * Proof Rule Application responsible for node.
     * Null for the root node.
     */
    private final @Nullable ProofRuleApplication ruleApplication;

    /**
     * Pointer to command that produced this node.
     * Null if root
     *
     * Can be set after construction.
     */
    private final @Nullable Command command;

    /**
     * Pointer to children; mutable
     */
    private @Nullable List<ProofNode> children;

    /**
     * Root PVC
     */
    private final PVC pvc;

    /**
     * Sequent in this proof node
     */
    private final @NonNull Sequent sequent;

    /**
     * The label a rule application has given this Node on application.
     * (see {@link BranchInfo#getLabel()}).
     * null for the root.
     */
    private final @Nullable String label;

    /**
     * The symbols added by a rule application
     */
    private final @NonNull SymbolTable addedSymbols;


    public static ProofNode createRoot(PVC pvc) {
        return new ProofNode(null, null, null, null,
                pvc.getSequent(), pvc);
    }

    public static ProofNode createChild(ProofNode parent, ProofRuleApplication pra,
                                        String label, Command command, Sequent seq) {
        return new ProofNode(parent, pra, label, command, seq, parent.getPVC());
    }

    public static ProofNode createClosureChild(ProofNode parent, ProofRuleApplication pra,
                                               Command command) {
        return new ProofNode(parent, pra, "*closed*", command, Sequent.EMPTY, parent.getPVC());
    }

    // TODO Make this private and call it with reflection from test cases to hide it.
    public ProofNode(ProofNode parent, ProofRuleApplication pra,
                     String label, Command command, Sequent seq, PVC rootPVC) {
        this.parent = parent;
        this.ruleApplication = pra;
        this.label = label;
        this.sequent = seq;
        this.pvc = rootPVC;
        this.command = command;
        this.addedSymbols = new MapSymbolTable(Collections.emptyList());
    }

    public SymbolTable getAllSymbols() {
        if(parent != null) {
            return new MapSymbolTable(parent.getAllSymbols(), addedSymbols.getAllSymbols());
        } else {
            return new MapSymbolTable(pvc.getSymbolTable(), addedSymbols.getAllSymbols());
        }
    }

    /**
     * This is essential and needed for proof construction, otherwise the proofnodemanager has no chance to add children
     *
     * @param children
     */
    public void setChildren(List<ProofNode> children) {
        this.children = new ArrayList<>(children);
    }

    /**
     * Is this node closed?
     *
     * This is the case if the node has been interpreted and has no children.
     *
     * @return true iff the script node is a closed proof leaf.
     */
    public boolean isClosed() {
        return children != null && children.isEmpty();
    }

    /**
     * Returns true if there is no open leaf in the tree beneath
     *
     * @return true if the spanned subtree is closed.
     */
    public boolean allLeavesClosed() {
        return children != null && children.stream().allMatch(ProofNode::allLeavesClosed);
    }

    public String getLabel() {
        return label;
    }

    public Command getCommand() {
        return command;
    }

    public Sequent getSequent() {
        return sequent;
    }

    public ProofNode getParent() {
        return parent;
    }

    public PVC getPVC() {
        return pvc;
    }

    public ProofRuleApplication getProofRuleApplication() {
        return ruleApplication;
    }

    /**
     * Get the list of all children of this proof node.
     * This returns null during script interpretation as the proof tree grows
     *
     * @return an immutable view to the list of children, null if not yet fully expanded
     * @see #getSuccessors()
     */
    public @Nullable List<ProofNode> getChildren() {
        return children == null ? null : Collections.unmodifiableList(children);
    }

    /**
     * Get the list of all children of this proof node.
     * While the children reference may be null, this will always return a valid object reference.
     * In case of children==null, it returns an empty list.
     *
     * @return an immutable view to the list of children, empty if not yet fully expanded
     * @see #getChildren()
     */
    public List<ProofNode> getSuccessors() {
        return children == null ? Collections.emptyList() : Collections.unmodifiableList(children);
    }

    public SymbolTable getAddedSymbols() {
        return addedSymbols;
    }
}
