/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.Sequent;

import java.util.Collections;

public class FakeSMTSolverRule extends AbstractProofRule {

    private static final ParameterDescription<Boolean> CLOSE_PARAM =
            new ParameterDescription<>( "close", ParameterType.BOOLEAN,false);

    public FakeSMTSolverRule() {
        super(CLOSE_PARAM);
    }

    @Override
    public String getName() {
        return "fake";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters)
            throws RuleException {

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setRefiner((x,y) -> refine(x, target.getSequent()));
        return builder.build();
    }


    private ProofRuleApplication refine(ProofRuleApplication app, Sequent sequent) {

        boolean decision = sequent.toString().hashCode() % 2 == 0;

        if (!decision) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        } else {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setRefiner(null)
                    .setApplicability(Applicability.APPLICABLE)
                    .setClosing();
            return builder.build();
        }
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        boolean decision;
        if(parameters.hasValue(CLOSE_PARAM)) {
            decision = parameters.getValue(CLOSE_PARAM);
        } else {
            decision
                    = target.getSequent().toString().hashCode() % 2 == 0;
        }

        if (!decision) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setRefiner(null)
                .setApplicability(Applicability.APPLICABLE)
                .setClosing();

        return builder.build();
    }

}
