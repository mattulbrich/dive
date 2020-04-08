/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;

/**
 * A kind of proof rule.
 *
 * A focus rule requires an "on" parameter to be set and cannot be applied if
 * there is no such parameter set.
 *
 * It is a {@link NotApplicableException} if it is not specified ... not only a
 * {@link ProofRuleApplication} with {@link edu.kit.iti.algover.rules.ProofRuleApplication.Applicability#INSTANTIATION_REQUIRED}.
 *
 * @author Mattias Ulbrich
 *
 * TODO MERGE THIS WITH DefaultFocusProofRule
 *
 */
public abstract class FocusProofRule extends AbstractProofRule {

    /**
     * The on-parameter is a required parameter in focus rules
     */
    public static final ParameterDescription<TermParameter> ON_PARAM_REQ =
            new ParameterDescription<>("on", ParameterType.TERM, true);

    public FocusProofRule(ParameterDescription<?>... parameters) {
        super(ON_PARAM_REQ, parameters);
    }

    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        if(selection == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        try {
            Parameters params = new Parameters();
            params.putValue(ON_PARAM_REQ, new TermParameter(selector, target.getSequent()));
            ProofRuleApplication result = makeApplication(target, params);
            return result;
        } catch (NotApplicableException e) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        if (!parameters.hasValue(ON_PARAM_REQ)) {
            throw new NotApplicableException("Missing parameter: on");
        }
        return super.makeApplication(target, parameters);
    }
}
