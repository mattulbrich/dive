/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
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
     * Proof Rule Application responsible for node
     */
    private final ProofRuleApplication ruleApplication;

    // private ProofHistory history;

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
     * Pointer to command that produced this node.
     * Null if root
     *
     * Can be set after construction.
     */
    private @Nullable Command command;

    /**
     * The label a rule application has given this Node on application.
     * (see {@link BranchInfo#label}).
     * null for the root.
     */
    private final @Nullable String label;

    /**
     * The symbols added by a rule application
     */
    private final @NonNull SymbolTable addedSymbols;


    public static ProofNode createRoot(PVC pvc) {
        return new ProofNode(null, null, null, null, pvc.getSequent(), pvc);
    }

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

    public Sequent getSequent() {
        return sequent;
    }

    public ProofNode getParent() {
        return parent;
    }

    public ProofRuleApplication getProofRuleApplication() {
        return ruleApplication;
    }

    public List<ProofNode> getChildren() {
        return children;
    }

    public SymbolTable getAddedSymbols() {
        return addedSymbols;
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
        this.children = children;
    }

    public PVC getPVC() {
        return pvc;
    }

    public boolean isClosed() {
        return children != null && children.isEmpty();
    }

    /**
     * Returns true if there is no leaf in the tree beneath that is an open goal
     *
     * @return true if the spanned subtree is closed.
     */
    public boolean allLeavesClosed() {
        return children != null && children.stream().allMatch(ProofNode::allLeavesClosed);
    }

//    @Override
//    public String toString() {
//        StringBuilder sb = new StringBuilder();
//     //   sb.append("\n==============================================================\n");
//        if (this.getParent() == null) {
//            sb.append("Root Node:\n");
//        } else {
//            sb.append("Proof Node:\n");
//        }
//
//        if (!this.variableAssignments.isEmpty()) {
//            //sb.append("Variable Assignments");
//            sb.append(variableAssignments.toString());
//        } else {
//            sb.append("Empty Assignments\n");
//        }
//        sb.append("\nSequent:\n" + this.sequent.toString() + "\n");
//        sb.append("\nMutator for this Node: ");
//        if (!mutator.isEmpty()) {
//            sb.append("\nMutator-Type: " + mutator.get(0).getNodeName()+"\n");
//
//            sb.append("\n" + mutator.get(0).getRuleContext().getText()+"\n");
//            if (mutator.size() != 1)
//                sb.append("\nNumber of Mutators: " + mutator.size()+"\n");
//        }
//       // sb.append("\n==============================================================\n");
//
//        return sb.toString();
//    }

    public String getLabel() {
        return label;
    }

    public Command getCommand() {
        return command;
    }

    public void setCommand(Command command) {
        this.command = command;
    }
}
