/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.kit.iti.algover.rules.Parameters.TypedValue;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;

public abstract class AbstractProofRule implements ProofRule {

    private Map<String, Class<?>> requiredParameters;
    private Map<String, Class<?>> optionalParameters;

    public AbstractProofRule(Map<String, Class<?>> requiredParameters, Map<String, Class<?>> optionalParameters) {
        this.requiredParameters = requiredParameters;
        this.optionalParameters = optionalParameters;
    }

    protected final void checkParameters(Parameters parameters) throws RuleException {
        Set<String> required = new HashSet<>(requiredParameters.keySet());
        for (Map.Entry<String, TypedValue<?>> en : parameters.entrySet()) {
            Class<?> t = requiredParameters.get(en.getKey());
            if(t == null) {
                t = optionalParameters.get(en.getKey());
            }

            if(t == null) {
                throw new RuleException("Unknown parameter '" + en.getKey() + "'");
            }

            TypedValue<?> value = en.getValue();
            if (!value.isType(t)) {
                throw new RuleException(
                        "Parameter " + en.getKey() + " has type " + value.getType() +
                        ", but I expected " + t);
            }

            required.remove(en.getKey());
        }

        if(!required.isEmpty()) {
            throw new RuleException("Missing required arguments: " + required);
        }
    }

}
