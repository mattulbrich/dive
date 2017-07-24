/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;

public abstract class AbstractProofRule<P> implements ProofRule<P> {

    protected void notApplicable() {
        new ProofRuleApplication<>(this, ChangeInfo.UNCHANGED,
                Applicability.NOT_APPLICABLE, getName(), null);
    }

}
