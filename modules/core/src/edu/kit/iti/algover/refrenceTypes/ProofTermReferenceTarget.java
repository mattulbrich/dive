package edu.kit.iti.algover.refrenceTypes;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.TermSelector;

/**
 * For references that point to terms (or subterms) of a sequent
 * in a proof.
 * <p>
 * Targets are identified by the path through proof nodes and
 * a TermSelector for identifying the subterm within that proof
 * node's sequent.
 * <p>
 * Created by Philipp on 27.08.2017.
 */
public class ProofTermReferenceTarget extends ReferenceTarget {

    private final ProofNodeSelector proofNodeSelector;
    private final TermSelector termSelector;

    public ProofTermReferenceTarget(ProofNodeSelector proofNodeSelector, TermSelector termSelector) {
        this.proofNodeSelector = proofNodeSelector;
        this.termSelector = termSelector;
    }

    @Override
    public <R> R accept(ReferenceTargetVisitor<R> visitor) {
        return visitor.visit(this);
    }

    public ProofNodeSelector getProofNodeSelector() {
        return proofNodeSelector;
    }

    public TermSelector getTermSelector() {
        return termSelector;
    }

}
