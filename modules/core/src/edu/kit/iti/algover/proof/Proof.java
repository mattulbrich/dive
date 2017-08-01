package edu.kit.iti.algover.proof;

/**
 * Proof Object
 */
public class Proof {
    /**
     * Status of Proof
     */
    private ProofStatus proofStatus;

    /**
     * Root of logical Proof
     */
    private ProofNode proofRoot;

    /**
     * Root of Script
     */
    //private ScriptASTNode scriptRoot;
    public ProofStatus getProofStatus() {
        return proofStatus;
    }

    public void setProofStatus(ProofStatus proofStatus) {
        this.proofStatus = proofStatus;
    }


    /**
     * Replay proof
     *
     * @return
     */
    public Proof replay() {
        return this;
    }
}
