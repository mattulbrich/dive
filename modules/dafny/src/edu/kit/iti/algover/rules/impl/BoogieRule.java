/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
// Checkstyle: ALLOFF

package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.boogie.BoogieProcess;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;

import java.nio.channels.ClosedByInterruptException;

/*
 * This is a quick and dirty implementation until the real one is available
 * Code quality is lower than elsewhere since this is a temporary implementation.
 */
public class BoogieRule extends AbstractProofRule {

    @Override
    public String getName() {
        return "boogie";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        // TODO change ?
        // builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setApplicability(Applicability.APPLICABLE);
        builder.setClosing();
        builder.setRefiner((app, param) -> refine(target, app));
        return builder.build();
    }

    private ProofRuleApplication refine(ProofNode target, ProofRuleApplication app) throws RuleException {
        PVC pvc = target.getPVC();

        if (isValid(target)) {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setApplicability(Applicability.APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        } else {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setApplicability(Applicability.NOT_APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        }

    }

    @Override
    public ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {

        if (isValid(target)) {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
            builder.setApplicability(Applicability.APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        } else {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
            builder.setApplicability(Applicability.NOT_APPLICABLE);
            builder.setRefiner(null);
            return builder.build();
        }
    }

    private boolean isValid(ProofNode target) throws RuleException {

        PVC pvc = target.getPVC();

        BoogieProcess process = new BoogieProcess(pvc.getProject());

        process.setSymbolTable(pvc.getSymbolTable());

        process.setSequent(target.getSequent());

        try {
            return process.callBoogie();
        } catch(RuleException rex) {
            throw rex;
        } catch (ClosedByInterruptException e) {
            return false;
        } catch(Exception ex) {
            throw new RuleException("The call to Boogie was not successful", ex);
        }

    }

}