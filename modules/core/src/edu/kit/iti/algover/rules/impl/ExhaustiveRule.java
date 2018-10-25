package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collector;
import java.util.stream.Collectors;


/**
 * Created by jonasklamroth on 22.08.18.
 */
public class ExhaustiveRule extends AbstractProofRule {
    static ParameterDescription<String> ruleName = new ParameterDescription<>("ruleName", ParameterType.STRING, true);

    public ExhaustiveRule() {
        super(ruleName, ON_PARAM);
    }

    @Override
    public String getName() {
        return "exhaustive";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        String rn = parameters.getValue(ruleName);

        if(rn == null) {
            return new ProofRuleApplicationBuilder(this).build();
        }

        List<ProofRule> rules = target.getPVC().getProject().getAllProofRules().stream().filter(
                proofRule -> { return proofRule.getName() == rn; }
        ).collect(Collectors.toList());
        assert(rules.size() == 1);

        ProofRule rule = rules.get(0);

        TermSelector onSelector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofRuleApplication res = applyRuleExhaustive(rule, target, onSelector);

        if(res == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        } else {
            ProofRuleApplicationBuilder top = new ProofRuleApplicationBuilder(this);
            top.newBranch();
            top.setApplicability(ProofRuleApplication.Applicability.APPLICABLE)
                    .setSubApplications(Collections.singletonList(res));
            return top.build();
        }
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        String rn = parameters.getValue(ruleName);

        List<ProofRule> rules = target.getPVC().getProject().getAllProofRules().stream().
                filter(proofRule -> { return proofRule.getName().equals(rn); }).
                collect(Collectors.toList());
        assert(rules.size() == 1);

        ProofRule rule = rules.get(0);

        TermSelector onSelector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofRuleApplication res = applyRuleExhaustive(rule, target, onSelector);

        if(res == null) {
            throw new RuleException("exhaustive could not be applied.");
        } else {
            ProofRuleApplicationBuilder top = new ProofRuleApplicationBuilder(this);
            top.newBranch();
            top.setApplicability(ProofRuleApplication.Applicability.APPLICABLE)
                    .setSubApplications(Collections.singletonList(res));
            return top.build();
        }
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
