package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

import java.util.List;

/**
 * Created by sarah on 10/7/15.
 */
public interface ProofStep {

    public ProofStepResult apply(ProofFormula form, Term t, List<ProofFormula> side_conditions);

    public boolean possibleApplications(ProofFormula form, Term t, List<ProofFormula> side_conditions);

    public String getRuleName();

    public String getCategory();


}
