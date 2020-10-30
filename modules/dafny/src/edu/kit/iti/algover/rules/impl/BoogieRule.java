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
import edu.kit.iti.algover.rules.NoFocusProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;

import java.nio.channels.ClosedByInterruptException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/*
 * This is a quick and dirty implementation until the real one is available
 * Code quality is lower than elsewhere since this is a temporary implementation.
 */
public class BoogieRule extends NoFocusProofRule {

    @Override
    public String getName() {
        return "boogie";
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(Applicability.MAYBE_APPLICABLE);
        builder.setClosing();
        builder.setRefiner((app, param) -> refine(target, app));
        return builder.build();
    }

    private ProofRuleApplication refine(ProofNode target, ProofRuleApplication app) throws RuleException {
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

    private boolean isValid(ProofNode target) throws RuleException {

        PVC pvc = target.getPVC();

        BoogieProcess process = new BoogieProcess(pvc.getProject(), pvc.getSymbolTable(), target);

        try {
            String hash = process.getHash();
            if(BoogieCache.contains(hash)) {
                return true;
            }
            boolean result = process.callBoogie();
            return result;
        } catch(RuleException rex) {
            throw rex;
        } catch (ClosedByInterruptException e) {
            return false;
        } catch(Exception ex) {
            throw new RuleException("The call to Boogie was not successful", ex);
        }
    }

}