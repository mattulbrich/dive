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

    public DefaultFocusProofRule(ParameterDescription<?>... parameters) {
        super(ON_PARAM, parameters);
    }

    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {

        try {
            Parameters params = new Parameters();
            if (selection != null) {
                params.putValue(ON_PARAM, new TermParameter(selector, target.getSequent()));
            }
            ProofRuleApplication result = makeApplication(target, params);
            return result;
        } catch (NotApplicableException e) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        if (!parameters.hasValue(ON_PARAM)) {
            TermParameter defaultOnParameter = getDefaultOnParameter(target);
            parameters.putValue(ON_PARAM, defaultOnParameter);
        }

        return super.makeApplication(target, parameters);
    }

    protected abstract TermParameter getDefaultOnParameter(ProofNode target) throws RuleException;
}
