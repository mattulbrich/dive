package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

/**
 * Created by sarah on 10/7/15.
 */
public interface ProofStep {

    public ProofStepResult apply(ProofFormula form, Term t);

    public boolean canApply(Term t);

    public String getRuleName();

    public String getCategory();


}
