/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.concurrent.Callable;

import nonnull.NonNull;
import nonnull.Nullable;

public final class PotentialProofStep {

    public final static PotentialProofStep NEVER_APPLICABLE =
            new PotentialProofStep(null, null);

    public enum Applicability {
        APPLICABLE, SPLIT_APPLICABLE,
        MAYBE_APPLICABLE, NOT_APPLICABLE
    };

    private ProofStep result;

    private Callable<ProofStep> refiner;

    public PotentialProofStep(
            @Nullable ProofStep result,
            @Nullable Callable<ProofStep> refiner) {

        this.result = result;
        this.refiner = refiner;
    }

    public void refine() {
        if(refiner == null) {
            throw new Error(new NullPointerException());
        }
        try {
            result = refiner.call();
            refiner = null;
        } catch(Exception ex) {
            throw new Error(ex);
        }
    }

    public @Nullable ProofStep getResult() {
        return result;
    }

    public @NonNull Applicability getApplicability() {
        if(result == null) {
            if(refiner == null) {
                return Applicability.NOT_APPLICABLE;
            } else {
                return Applicability.MAYBE_APPLICABLE;
            }
        } else {
            if(result.countBranches() > 1) {
                return Applicability.SPLIT_APPLICABLE;
            } else {
                return Applicability.APPLICABLE;
            }
        }
    }

}
