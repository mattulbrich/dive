package edu.kit.iti.algover.util;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.term.Term;

public class HistoryProofUtils {


    @TestInfrastructure
    public static boolean compareTerms(ProofTermReferenceTarget child, ProofTermReferenceTarget parent, Proof proof) throws RuleException {
        return compareTerms(getTerm(child, proof), parent, proof);
    }

    @TestInfrastructure
    public static Term getTerm(ProofTermReferenceTarget target, Proof proof) throws RuleException {
        return  target.getTermSelector().selectSubterm(target.getProofNodeSelector().get(proof).getSequent());
    }

    @TestInfrastructure
    public static boolean compareTerms(Term termChild, ProofTermReferenceTarget target, Proof currentProof) throws RuleException {
        Term term = target.getTermSelector().selectSubterm(target.getProofNodeSelector().get(currentProof).getSequent());
        return termChild == term;

    }

}
