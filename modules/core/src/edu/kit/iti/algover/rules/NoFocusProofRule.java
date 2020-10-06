/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;

public abstract class NoFocusProofRule extends AbstractProofRule {

    /**
     * the mandatory version of the "on" parameter
     */
    public static final ParameterDescription<TermParameter> ON_PARAM =
            new ParameterDescription<>("on", ParameterType.TERM, true);

    public NoFocusProofRule(ParameterDescription<?>... parameters) {
        super(parameters);
    }

    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        if(selector == null) {
            return ProofRuleApplicationBuilder.instantiationRequired(this);
        }

        try {
            Parameters params = new Parameters();
            ProofRuleApplication result = makeApplication(target, params);
            return result;
        } catch (NotApplicableException e) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
    }

    @Override
    public final ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        return super.makeApplication(target, parameters);
    }
}
