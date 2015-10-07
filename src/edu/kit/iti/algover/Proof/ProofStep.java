package edu.kit.iti.algover.Proof;

/**
 * Created by sarah on 10/7/15.
 */
public interface ProofStep {

    public ProofStepResult applyProofStep();

    public String getRuleName();
}
