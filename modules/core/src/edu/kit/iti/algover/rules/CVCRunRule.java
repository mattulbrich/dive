/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.prettyprint.SubtermSelector;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.term.Sequent;

public class CVCRunRule implements ProofRule<CVCRunRule.CVCArgs> {

    public static class CVCArgs {
        @Parameter("to") int timeout;
    }

    @Override
    public String getName() {
        return "cvc";
    }

    @Override
    public PotentialProofStep consider(Sequent sequent, ProofFormula form, SubtermSelector selector) {
        return new PotentialProofStep((ProofStep)null, () -> {
            // CVCSolver solver = ...
            // solver.solve()...

            // TODO This is demo only ...
            try { Thread.sleep(2000); } catch(Exception ex) {}
            if(System.currentTimeMillis() % 2 == 0) {
                return null;
            } else {
                return ProofStep.closeStep();
            }
        });
    }

    @Override
    public ProofStep apply(Sequent sequent, CVCArgs arguments) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public CVCArgs parseArguments(ScriptTree tree) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getCategory() {
        // TODO Auto-generated method stub
        return null;
    }

}
