package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

import java.util.List;

/**
 * Interface for Propof steps
 * Proof steps can be single rules, but also application of solvers etc.
 */
public interface ProofStep {

    /**
     * @param form
     * @param t
     * @param side_conditions
     * @return
     */
    public ProofStepResult apply(ProofFormula form, Term t, List<ProofFormula> side_conditions);

    public boolean possibleApplications(ProofFormula form, Term t, List<ProofFormula> side_conditions);

    public String getRuleName();

    public String getCategory();



}
