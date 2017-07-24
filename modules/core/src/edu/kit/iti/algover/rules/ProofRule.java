/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.prettyprint.SubtermSelector;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.term.Sequent;

/**
 * Interface for Propof steps
 * Proof steps can be single rules, but also application of solvers etc.
 */
public interface ProofRule<A> {

    public String getName();

    public PotentialProofStep consider(Sequent sequent, ProofFormula form, SubtermSelector selector);

    public ProofStep apply(Sequent sequent, A arguments);

    public A parseArguments(ScriptTree tree);

    // REVIEW: unclear to me
    public String getCategory();
}
