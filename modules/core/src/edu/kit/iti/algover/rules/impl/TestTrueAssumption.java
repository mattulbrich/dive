/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.HashMap;

public class TestTrueAssumption extends AbstractProofRule {

    public TestTrueAssumption() {
        super();
    }

    @Override
    public String getName() {
        return "testTrueAssumption";
    }

    private ProofRuleApplication buildApplication() throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        try {
            builder.newBranch().addAdditionAntecedent(new ProofFormula(new ApplTerm(BuiltinSymbols.TRUE)));
        } catch (TermBuildException e) {
            throw new RuleException(e);
        }
        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        return buildApplication();
    }

}
