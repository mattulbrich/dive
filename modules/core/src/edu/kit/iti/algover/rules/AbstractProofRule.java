/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.beans.ParameterDescriptor;
import java.util.*;

import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;

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
     * The parameter "type" is used to describe whether or not a rule is applied
     * exhaustively, deep or globally.
     */
    public static final ParameterDescription<String> TYPE_PARAM =
            new ParameterDescription<>("type", ParameterType.STRING, false);

    /**
     * Whether or not this rule may be applied exhaustively.
     */
    protected boolean mayBeExhaustive = true;

    /**
     * Whether or not this rule may be applied deep exhaustively.
     */
    protected boolean mayBeDeep = true;

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
                if(en.getKey().equals("type") && en.getValue() instanceof String) {
                    allParameters.put("type", TYPE_PARAM);
                    t = allParameters.get(en.getKey());
                } else {
                    throw new RuleException("Unknown parameter '" + en.getKey() + "'");
                }
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

    protected ProofRuleApplicationBuilder handleControlParameters(Parameters params, Sequent s) throws RuleException {
        ProofRuleApplicationBuilder rab = new ProofRuleApplicationBuilder(this);
        return handleControlParameters(params, s, rab);
    }

    protected ProofRuleApplicationBuilder handleControlParameters(Parameters params, Sequent s, ProofRuleApplicationBuilder rab) throws RuleException {
        if(params.getValue("type") == null) {
            return rab;
        }

        switch ((String)params.getValue("type")) {
            case "exhaustive":
                if(!mayBeExhaustive) {
                    throw new RuleException("Rule " + getName() + " can not be applied exhaustively.");
                }
                rab.setExhaustive(true);
                break;
            case "deep":
                if(!mayBeExhaustive) {
                    throw new RuleException("Rule " + getName() + " can not be applied exhaustively.");
                }
                rab.setExhaustive(true);
                if(!mayBeDeep) {
                    throw new RuleException("Rule " + getName() + " can not be applied deep exhaustively.");
                }
                rab.setDeep(true);
                break;
            case "globalExhaustive":
                if(!mayBeExhaustive) {
                    throw new RuleException("Rule " + getName() + " can not be applied exhaustively.");
                }
                rab.setExhaustive(true);
                rab.setGlobal(true);
                break;
            case "globalDeep":
                rab.setGlobal(true);
                if(!mayBeExhaustive) {
                    throw new RuleException("Rule " + getName() + " can not be applied exhaustively.");
                }
                rab.setExhaustive(true);
                if(!mayBeDeep) {
                    throw new RuleException("Rule " + getName() + " can not be applied deep exhaustively.");
                }
                rab.setDeep(true);
                break;
            case "globalOnce":
                rab.setGlobal(true);
            case "once":
                break;
            default:
                throw new RuleException("Unknown rule application type: " + params.getValue("type") + ".");
        }

        Term t = params.getValue(ON_PARAM);
        Optional<TermSelector> ots = RuleUtil.matchSubtermInSequent(t::equals, s);
        if(ots.isPresent()) {
            rab.setOn(ots.get());
        }

        return rab;
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

    /**
     *
     * Generates a fitting transcript for the rule applied on the term selected by a TermSelector.
     *
     * @param ts the TermSelector
     * @param s the sequent to get the script for
     * @return a default transcript for the given parameters
     * @throws RuleException
     */
    protected final String getTranscript(TermSelector ts, Sequent s) throws RuleException {
        Term on = ts.selectSubterm(s);
        return getTranscript(new Pair<>("on", on));

    }

}
