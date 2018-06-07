/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.BranchInfoBuilder;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;

public class SkipRule extends AbstractProofRule {
    @Override
    public String getName() {
        return "skip";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder b = new ProofRuleApplicationBuilder(this);
        b.setApplicability(Applicability.APPLICABLE);
        BranchInfoBuilder br = b.newBranch();
        br.setLabel("continue");
        return b.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder b = new ProofRuleApplicationBuilder(this);
        b.setApplicability(Applicability.APPLICABLE);
        BranchInfoBuilder br = b.newBranch();
        br.setLabel("continue");
        return b.build();
    }
}
