/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;

public abstract class DefaultFocusProofRule extends AbstractProofRule {

    /**
     * The on-parameter is an optionl parameter in default-focus rules
     */
    public static ParameterDescription<TermParameter> ON_PARAM_OPT =
            new ParameterDescription<>("on", ParameterType.TERM, false);

    public DefaultFocusProofRule(ParameterDescription<?>... parameters) {
        super(ON_PARAM_OPT, parameters);
    }

    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {

        try {
            Parameters params = new Parameters();
            if (selection != null) {
                params.putValue(ON_PARAM_OPT, new TermParameter(selector, target.getSequent()));
            }
            ProofRuleApplication result = makeApplication(target, params);
            return result;
        } catch (NotApplicableException e) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        if (!parameters.hasValue(ON_PARAM_OPT)) {
            TermParameter defaultOnParameter = getDefaultOnParameter(target);
            parameters.putValue(ON_PARAM_OPT, defaultOnParameter);
        }

        return super.makeApplication(target, parameters);
    }

    protected abstract TermParameter getDefaultOnParameter(ProofNode target) throws RuleException;
}
