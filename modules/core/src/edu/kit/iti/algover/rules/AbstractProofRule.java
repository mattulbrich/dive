/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.beans.ParameterDescriptor;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;

/**
 * This class should serve as base class for all {@link ProofRule} implementations.
 *
 * Its main feature is the possibility to check actual arguments against the formal parameters.
 *
 * @author Mattias Ulbrich
 */
public abstract class AbstractProofRule implements ProofRule {

    /**
     * The parameter for "on" is very common for rules.
     */
    public static final ParameterDescription<Term> ON_PARAM =
            new ParameterDescription<>("on", ParameterType.TERM, true);

    /**
     * The parameter "deep" is used for propositional rules that
     * are to be applied exhaustively.
     */
    public static final ParameterDescription<Boolean> DEEP_PARAM =
            new ParameterDescription<>("deep", ParameterType.BOOLEAN, false);

    /**
     * This map captures the parameters made
     * known to the class in the constructor.
     */
    private final Map<String, ParameterDescription<?>> allParameters = new HashMap<>();


    /**
     * Instantiate a new object.
     *
     * @param parameters a list of all parameters that this proof rule accepts.
     */
    public AbstractProofRule(ParameterDescription<?>... parameters) {
        for (ParameterDescription<?> p : parameters) {
            allParameters.put(p.getName(), p);
        }
    }

    /**
     * Check the actual parameters obtained as method parameter against the formal parameters stored
     * in {@link #allParameters},
     *
     * @param parameters the map of parameters against values.
     * @throws RuleException if a required parameter has been omitted or an unknown parameter has
     *                       been used
     */
    protected final void checkParameters(Parameters parameters) throws RuleException {
        Set<ParameterDescription<?>> required = new HashSet<>();
        for (ParameterDescription<?> p : allParameters.values()) {
            if(p.isRequired()) {
                required.add(p);
            }
        }

        for (Map.Entry<String, Object> en : parameters.entrySet()) {
            ParameterDescription<?> t = allParameters.get(en.getKey());

            if (t == null) {
                throw new RuleException("Unknown parameter '" + en.getKey() + "'");
            }

            Object value = en.getValue();
            if (!t.acceptsValue(value)) {
                throw new RuleException(
                        "ParameterDescription " + en.getKey() + " has class " + value.getClass() +
                                ", but I expected " + t + " (class " + t.getType() + ")");
            }

            required.remove(t);
        }

        if (!required.isEmpty()) {
            throw new RuleException("Missing required arguments: " + required);
        }
    }

    /**
     *
     * Generates a fitting transcript for the rule and the given parameters.
     *
     * @param params the parameters for which the transcript shoud be generated
     * @return a default transcript for the given parameters
     * @throws RuleException
     */
    protected final String getTranscript(Pair<String, Object>... params) throws RuleException {
        String res = getName();
        if(allParameters.size() == 0) {
            return res + ";";
        }
        Map<String, ParameterDescription<?>> required = new HashMap<>();
        for (String name : allParameters.keySet()) {
            if(allParameters.get(name).isRequired()) {
                required.put(name, allParameters.get(name));
            }
        }
        if(params.length < required.size()) {
            throw new RuleException(getName() + " needs at least " + required.size() +
                    " parameters but got only " + params.length);
        }
        for(Pair<String, Object> p : params) {
            if(!allParameters.containsKey(p.getFst())) {
                throw new RuleException("No parameter named " + p.getFst() + " for Rule " + getName());
            }
            if(!allParameters.get(p.getFst()).acceptsValue(p.getSnd())) {
                throw new RuleException(
                        "ParameterDescription " + p.getFst() + " has class " + p.getSnd().getClass() +
                                ", but I expected " + allParameters.get(p) +
                                " (class " + allParameters.get(p).getType() + ")");
            }
            res += " " + p.getFst() + "='" + p.getSnd() + "'";
            required.remove(p.getFst());
        }
        if (!required.isEmpty()) {
            throw new RuleException("Missing required arguments: " + required);
        }

        res += ";";
        return res;
    }

}
