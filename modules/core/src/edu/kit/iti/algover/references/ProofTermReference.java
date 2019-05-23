/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

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
public class ProofTermReference extends Reference {

    private final ProofNodeSelector proofNodeSelector;
    private final TermSelector termSelector;

    public ProofTermReference(ProofNodeSelector proofNodeSelector, TermSelector termSelector) {
        this.proofNodeSelector = proofNodeSelector;
        this.termSelector = termSelector;
    }

    @Override
    public <R> R accept(ReferenceVisitor<R> visitor) {
        return visitor.visit(this);
    }

    public ProofNodeSelector getProofNodeSelector() {
        return proofNodeSelector;
    }

    public TermSelector getTermSelector() {
        return termSelector;
    }

    @Override
    public String toString() {
        return "ProofTermReference{" +
                "proofNodeSelector=" + proofNodeSelector +
                ", termSelector=" + termSelector +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ProofTermReference)) return false;

        ProofTermReference that = (ProofTermReference) o;

        if (!proofNodeSelector.equals(that.proofNodeSelector)) return false;
        return termSelector.equals(that.termSelector);
    }

    @Override
    public int hashCode() {
        int result = proofNodeSelector.hashCode();
        result = 31 * result + termSelector.hashCode();
        return result;
    }
}
