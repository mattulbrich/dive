package edu.kit.iti.algover.proof;

/**
 * Created by sarah on 10/7/15.
 */
public class ProofNode {

    private ProofNode parent;
    private ProofStepResult psr;
    private ProofHistory history;

    public ProofNode(ProofNode parent, ProofStepResult psr, ProofHistory history){
        this.parent = parent;
        this.psr = psr;
        this.history = history;
    }
}
