/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
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
    public ProofRuleApplication consider(
            CVCArgs arguments,
            Sequent sequent,
            Sequent selection,
            TermSelector selector) {

        return new ProofRuleApplication<CVCArgs>(this, BranchInfo.UNCHANGED,
                Applicability.MAYBE_APPLICABLE, "cvc", () -> {
                    // CVCSolver solver = ...
                    // solver.solve()...

                    // TODO This is demo only ...
                    try { Thread.sleep(arguments.timeout); } catch(Exception ex) {}
                    if(System.currentTimeMillis() % 2 == 0) {
                        return new ProofRuleApplication<CVCArgs>(this, BranchInfo.UNCHANGED,
                                Applicability.NOT_APPLICABLE, "cvc", null);
                    } else {
                        return new ProofRuleApplication<CVCArgs>(this, BranchInfo.CLOSE,
                                Applicability.APPLICABLE, "cvc", null);
                    }
                });
    }

    @Override
    public CVCArgs parseArguments(ScriptTree tree) {
        // TODO Auto-generated method stub
        return null;
    }

}
