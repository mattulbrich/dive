/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;

public abstract class AbstractProofRule<P> implements ProofRule<P> {

    protected final ProofRuleApplication<P> notApplicable() {
        return new ProofRuleApplication<>(this, BranchInfo.UNCHANGED,
                Applicability.NOT_APPLICABLE, getName(), null);
    }

}
