/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.proof.ProofFormula;

public class ParallelUpdateSequenter extends UpdateSequenter {

    @Override
    public String getName() {
        return "ass-parallel";
    }

    @Override
    public String getDescriptiveName() {
        return "Parallel assignments in front of every formula";
    }

    @Override
    protected ProofFormula postProcess(ProofFormula formula) {
        throw new UnsupportedOperationException("not yet implemented");
    }
}
