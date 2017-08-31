/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

public interface Refiner {

    ProofRuleApplication refine(ProofRuleApplication original, Parameters additionalParameters);

}