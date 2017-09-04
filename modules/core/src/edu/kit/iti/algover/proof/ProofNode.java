/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.term.Sequent;

import java.util.LinkedList;
import java.util.List;

/**
 * Class represents one proof node. It has a pointer to its parent node and to the children nodes.
 * If no child node exists, the node is either a leaf in the proof tree or a closed branch
 * (is that a good idea, or should we incorporate a field that is true when node is a closed proof node?)
 * *
 */
public class ProofNode {

    private ProofNode parent;


    private ProofRuleApplication psr;

    private ProofHistory history;

    private List<ProofNode> children;

    private PVC rootPVC;

    private Sequent sequent;


    private boolean isclosed;
    private ASTNode mutator;

    public ProofNode(ProofNode parent, ProofRuleApplication psr, ProofHistory history, Sequent seq, PVC rootPVC) {
        this.parent = parent;
        this.psr = psr;
        this.history = history;
        this.children = new LinkedList<ProofNode>();
        this.sequent = seq;
        this.rootPVC = rootPVC;
        isclosed = false;
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

    public void setPsr(ProofRuleApplication psr) {
        this.psr = psr;
    }

    public ProofHistory getHistory() {
        return history;
    }

    public List<ProofNode> getChildren() {
        return children;
    }

    public void setChildren(List<ProofNode> children) {
        this.children = children;
    }

    public PVC getRootPVC() {
        return rootPVC;
    }

    public boolean isIsclosed() {
        return isclosed;
    }

    public void setIsclosed(boolean isclosed) {
        this.isclosed = isclosed;
    }

    public void setSequent(Sequent sequent) {
        this.sequent = sequent;
    }

    public ASTNode getMutator() {
        return mutator;
    }

    public void setMutator(ASTNode mutator) {
        this.mutator = mutator;
    }
}
