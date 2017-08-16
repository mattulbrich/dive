/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.Collections;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.Sequent;

public class FakeSMTSolverRule extends AbstractProofRule {

    public FakeSMTSolverRule() {
        super(Collections.emptyMap(), Collections.emptyMap());
    }

    @Override
    public String getName() {
        return "fake";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector)
            throws RuleException {

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setRefiner(this::refine);
        return builder.build();
    }


    private ProofRuleApplication refine(ProofRuleApplication app, Parameters addParams) {

        // TODO This is demo only ...
        try { Thread.sleep(2000); } catch(Exception ex) {}

        if(System.currentTimeMillis() % 2 == 0) {
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
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {

        if(parameters.getValue("fake") == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setRefiner(null)
            .setApplicability(Applicability.APPLICABLE)
            .setClosing();

        return builder.build();
    }

}
