/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

public interface Refiner {

    ProofRuleApplication refine(ProofRuleApplication original, Parameters additionalParameters) throws RuleException;

}
