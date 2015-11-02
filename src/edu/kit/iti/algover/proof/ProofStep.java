package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.term.Term;

/**
 * Created by sarah on 10/7/15.
 */
public interface ProofStep {

    public ProofStepResult apply(Term t);

    public Boolean canApply(Term t);

    public String getRuleName();

    public String getCategory();


}
