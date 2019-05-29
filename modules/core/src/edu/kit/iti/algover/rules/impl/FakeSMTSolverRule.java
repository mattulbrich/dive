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

import java.math.BigInteger;
import java.util.Collections;

public class FakeSMTSolverRule extends AbstractProofRule {

    private static final ParameterDescription<Boolean> CLOSE_PARAM =
            new ParameterDescription<>( "close", ParameterType.BOOLEAN,false);

    private static final ParameterDescription<BigInteger> SLEEP_PARAM =
            new ParameterDescription<>( "sleep", ParameterType.INTEGER,false);

    public FakeSMTSolverRule() {
        super(CLOSE_PARAM, SLEEP_PARAM);
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

        if(parameters.hasValue(SLEEP_PARAM)) {
            int time = parameters.getValue(SLEEP_PARAM).intValue();
            try {
                Thread.sleep(time);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setRefiner(null)
                .setApplicability(Applicability.APPLICABLE)
                .setClosing();

        return builder.build();
    }

}
