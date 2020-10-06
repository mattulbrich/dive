/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import nonnull.DeepNonNull;
import nonnull.Nullable;

/**
 * Default implementation of the proof rules that focus on a term.
 *
 * Here the "on" parameter is mandatory.
 *
 * It add default implementations for {@link #considerApplication(ProofNode, Sequent, TermSelector)}
 * and {@link #makeApplication(ProofNode, Parameters)}
 *
 * There is a method {@link #getDefaultOnParameter(ProofNode)} which for all
 * implementations has to yield the default value for the on parameter (e.g.
 * '|- _ && _' for andRight).
 *
 * @author Mattias Ulbrich
 *
 * TODO MERGE THIS WITH FocusProofRule
 */
public abstract class DefaultFocusProofRule extends AbstractProofRule {

    /**
     * The on-parameter is an optional parameter in default-focus rules
     */
    public static final ParameterDescription<TermParameter> ON_PARAM_OPT =
            new ParameterDescription<>("on", ParameterType.TERM, false);

    /**
     * Instantiate a new instance with the given set of parameters.
     *
     * "on" is always a required parameter for this subclasses of this class.
     *
     * @param parameters the list of parameters for this class
     */
    public DefaultFocusProofRule(@DeepNonNull ParameterDescription<?>... parameters) {
        super(ON_PARAM_OPT, parameters);
    }

    @Override
    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        if(selector == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

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

    /**
     * The "on"-parameter is mandatory for focus rules. However, it needs not be
     * mentioned explicitly in all cases.
     *
     * If "on" is omitted, the value returned by this method is used as value.
     *
     * @param target the proofnode for which the parameter is created
     * @return a term parameter containing the default value for "on", null if not supported
     * @throws RuleException if something goes wrong during computation
     */
    protected abstract @Nullable TermParameter getDefaultOnParameter(ProofNode target) throws RuleException;
}
