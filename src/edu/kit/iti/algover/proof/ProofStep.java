package edu.kit.iti.algover.proof;

/**
 * Created by sarah on 10/7/15.
 */
public interface ProofStep {

    public ProofStepResult apply();

    public Boolean canApply();

    public String getRuleName();

    public String getCategory();


}
