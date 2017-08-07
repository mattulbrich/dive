/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.term.Sequent;

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

    public ProofNode(ProofNode parent, ProofRuleApplication psr, ProofHistory history){
        this.parent = parent;
        this.psr = psr;
        this.history = history;
        this.children = new LinkedList<ProofNode>();
    }

    public Sequent getSequent() {
        return sequent;
    }
}
