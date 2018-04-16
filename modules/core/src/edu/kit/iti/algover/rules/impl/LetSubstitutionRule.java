/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * A built-in rule that can be applied to let-terms inline all their bound variables via substitution.
 * <p>
 * (see {@link SubstitutionVisitor} for an example.)
 *
 * @author philipp
 */
public class LetSubstitutionRule extends AbstractProofRule {

    /**
     * Builds a new SubstitutionRule.
     * <p>
     * This rule only requires the "on" parameter, the term that it should be applied on.
     * That term <strong>must</strong> be a let term.
     */
    public LetSubstitutionRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "substitute";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Term targetTerm = selector.selectSubterm(selection);
        if (!(targetTerm instanceof LetTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        LetTerm targetLet = (LetTerm) targetTerm;

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        builder.newBranch()
                .addReplacement(selector, applyLetSubstitution(targetLet));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE)
                .setTranscript(getName() + " on='" +
                        selector.selectSubterm(target.getSequent()) +  "';");

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);

        Term on = parameters.getValue(ON_PARAM);

        if (!(on instanceof LetTerm)) {
            throw new RuleException("Given term is not a let term");
        }

        LetTerm targetLet = (LetTerm) on;

        TermSelector selector = RuleUtil.matchSubtermInSequent(targetLet::equals, target.getSequent())
                .orElseThrow(() -> new RuleException("Could not find 'on' term"));

        ProofRuleApplicationBuilder builder = handleControlParameters(parameters, target.getSequent());

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        builder.newBranch().addReplacement(selector, applyLetSubstitution(targetLet));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE)
                .setTranscript(getName() + " on='" +
                        selector.selectSubterm(target.getSequent()) +  "';");

        return builder.build();
    }

    private static Term applyLetSubstitution(LetTerm targetLet) {
        Map<String, Term> substitutionMap =
                targetLet.getSubstitutions()
                        .stream()
                        .collect(Collectors.toMap(pair -> pair.fst.getName(), pair -> pair.snd));

        Term inner = targetLet.getTerm(0);
        return inner.accept(new SubstitutionVisitor(), substitutionMap);
    }
}
