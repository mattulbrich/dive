/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;


/**
 * Created by jonasklamroth on 22.08.18.
 */
public class ExhaustiveRule extends FocusProofRule {
    public static final ParameterDescription<String> RULE_NAME_PARAM =
            new ParameterDescription<>("RULE_NAME_PARAM", ParameterType.STRING, true);

    public ExhaustiveRule() {
        super(RULE_NAME_PARAM);
    }

    @Override
    public String getName() {
        return "exhaustive";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        String rn = parameters.getValue(RULE_NAME_PARAM);

        if (rn == null) {
            throw NotApplicableException.requiresParameter(this, RULE_NAME_PARAM);
        }

        List<ProofRule> rules = target.getPVC().getProject().getAllProofRules().stream().
                filter(proofRule -> { return proofRule.getName().equals(rn); }).
                collect(Collectors.toList());

        if (rules.isEmpty()) {
            throw new NotApplicableException("Unknown rule " + rn);
        }

        assert rules.size() == 1;

        ProofRule rule = rules.get(0);
        if (rule.getAllParameters().size() > 1) {
            throw new NotApplicableException("Only rules with 1 Parameter are exhaustively applicable.");
        }

        TermSelector onSelector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofRuleApplication res = applyRuleExhaustive(rule, target, onSelector);

        ProofRuleApplicationBuilder top = new ProofRuleApplicationBuilder(this);
        top.newBranch();
        // REVIEW: Nothing happens on this branch? No modification?

        top.setApplicability(ProofRuleApplication.Applicability.APPLICABLE)
                .setSubApplications(Collections.singletonList(res));
        return top.build();
    }

    private static ProofRuleApplication applyRuleExhaustive(ProofRule proofRule, ProofNode pn, TermSelector ts)  throws RuleException {
        ProofRuleApplication proofRuleApplication = new ProofRuleApplicationBuilder(proofRule)
                .setApplicability(ProofRuleApplication.Applicability.NOT_APPLICABLE)
                .build();
        if(ts.isValidForSequent(pn.getSequent())) {
            proofRuleApplication = proofRuleApplication.getRule().considerApplication(pn, pn.getSequent(), ts);
        }

        List<ProofNode> nodes;
        if (proofRuleApplication.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
            nodes = RuleApplicator.applyRule(proofRuleApplication, pn);
        } else {
            return null;
        }

        ProofRuleApplicationBuilder res = new ProofRuleApplicationBuilder(proofRuleApplication);
        List<ProofRuleApplication> subApplications = new ArrayList<>();
        for (ProofNode node : nodes) {
            subApplications.add(applyRuleExhaustive(proofRuleApplication.getRule(), node, ts));
        }
        res.setSubApplications(subApplications);


        return res.build();
    }
}
