package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.script.ast.ASTNode;
import javafx.beans.property.SimpleObjectProperty;

/**
 * Proof Object
 * This object contains the proof root as well as teh script root
 */
public class Proof {


    /**
     * Status of Proof
     */
    //private ProofStatus proofStatus;

    private SimpleObjectProperty<ProofStatus> proofStatus = new SimpleObjectProperty<>(null, "ProofStatusProperty");
    /**
     * Root of logical Proof
     */
    private ProofNode proofRoot;



    /**
     * Root of Script
     */
    private ASTNode scriptRoot;

    /**
     * PVC Name for which this proof object is created
     */
    private String pvcName;



    public Proof(String pvcName) {
        this.setPvcName(pvcName);
        this.setProofRoot(null);
        this.setProofRoot(null);
        this.setProofStatus(ProofStatus.NOT_LOADED);

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

    public SimpleObjectProperty<ProofStatus> proofStatusProperty() {
        return proofStatus;
    }

    /**
     * Replay proof
     *
     * @return
     */
    public Proof replay() {
        if (getProofStatus().equals(ProofStatus.DIRTY)) {
            //reload
            //
            setProofStatus(ProofStatus.OPEN);
        } else {
            setProofStatus(ProofStatus.NON_EXISTING);
        }
        return this;
    }

    public ProofStatus getProofStatus() {
        return proofStatus.get();
    }

    public void setProofStatus(ProofStatus proofStatus) {
        this.proofStatus.set(proofStatus);
    }

    public ASTNode getScriptRoot() {
        return scriptRoot;
    }

    public void setScriptRoot(ASTNode scriptRoot) {
        this.scriptRoot = scriptRoot;
    }
}
