package edu.kit.iti.algover.proof;

import java.util.LinkedList;

/**
 * Class represents one proof node. It has a pointer to its parent node and to the children nodes.
 * If no child node exists, the node is either a leaf in the proof tree or a closed branch
 * (is that a good idea, or should we incorporate a field that is true when node is a closed proof node?)
 * *
 */
public class ProofNode {

    private ProofNode parent;
    private ProofStepResult psr;
    private ProofHistory history;
    private LinkedList<ProofNode> children;

    public ProofNode(ProofNode parent, ProofStepResult psr, ProofHistory history){
        this.parent = parent;
        this.psr = psr;
        this.history = history;
        this.children = new LinkedList<ProofNode>();
    }
}
