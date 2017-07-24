/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.rules.ProofStep;

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
    private ProofStep psr;
    private ProofHistory history;
    private List<ProofNode> children;
    private PVC rootPVC;



    public ProofNode(ProofNode parent, ProofStep psr, ProofHistory history){
        this.parent = parent;
        this.psr = psr;
        this.history = history;
        this.children = new LinkedList<ProofNode>();
    }
}
