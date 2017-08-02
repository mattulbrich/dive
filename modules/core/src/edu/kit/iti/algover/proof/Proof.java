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

    private String pvcName;

    public ProofStatus getProofStatus() {
        return proofStatus;
    }

    public void setProofStatus(ProofStatus proofStatus) {
        this.proofStatus = proofStatus;
    }

    public ProofNode getProofRoot() {
        return proofRoot;
    }

    public void setProofRoot(ProofNode proofRoot) {
        this.proofRoot = proofRoot;
    }

    public String getPvcName() {
        return pvcName;
    }

    public void setPvcName(String pvcName) {
        this.pvcName = pvcName;
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
