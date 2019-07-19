/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules.impl;

// TODO DOC
public final class ProofRuleCategories {

    public static final String UNKNOWN = "Unknown";

    // TODO DOC
    public static final String PROPOSITIONAL = "Propositional";
    public static final String SIMPLIFICATIONS = "Simplifications";
    public static final String DEBUG = "Debug";

    private ProofRuleCategories() {
        throw new Error("not to be instantiated");
    }
}

