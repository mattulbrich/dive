/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.beans.ParameterDescriptor;
import java.util.*;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;
import jdk.nashorn.internal.ir.BreakableNode;

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
    public static final ParameterDescription<String> TYPE_PARAM =
            new ParameterDescription<>("type", ParameterType.STRING, false);

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
    private final void checkParameters(Parameters parameters) throws RuleException {
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

    protected Parameters extractParameters(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Parameters params = new Parameters();
        if(selector != null) {
            Term on = selector.selectSubterm(selection);
            params.putValue("on", on);
        }
        return params;
    }

    protected abstract ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException;

    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Parameters params = extractParameters(target, selection, selector);
        return considerApplication(target, params);
    }

    public final ProofRuleApplication considerApplication(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication pra = considerApplicationImpl(target, parameters);
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(pra);
        if(pra.getApplicability() == ProofRuleApplication.Applicability.APPLICABLE) {
            builder.setTranscript(getTranscript(pra, parameters));
        }
        return builder.build();
    }


    protected abstract ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException;

    public final ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);
        ProofRuleApplication pra = makeApplicationImpl(target, parameters);
        String transcript = getTranscript(pra, parameters);
        return new ProofRuleApplicationBuilder(pra).setTranscript(transcript).build();
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
                rab.setExhaustive(true);
                break;
            case "deep":
                rab.setExhaustive(true);
                rab.setDeep(true);
                break;
            case "global":
                rab.setExhaustive(true);
                rab.setGlobal(true);
                break;
            case "globalDeep":
                rab.setGlobal(true);
                rab.setExhaustive(true);
                rab.setDeep(true);
                break;
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
     * @param params the parameters for which the transcript should be generated
     * @return a valid transcript for the given parameters
     * @throws RuleException
     */
    private final String getTranscript(ProofRuleApplication pra, Parameters params) throws RuleException {
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
        if(params.entrySet().size() < required.size()) {
            throw new RuleException(getName() + " needs at least " + required.size() +
                    " parameters but got only " + params.entrySet().size());
        }
        for(Map.Entry<String, Object> p : params.entrySet()) {
            if(!allParameters.containsKey(p.getKey())) {
                throw new RuleException("No parameter named " + p.getKey() + " for Rule " + getName());
            }
            if(!allParameters.get(p.getKey()).acceptsValue(p.getValue())) {
                throw new RuleException(
                        "ParameterDescription " + p.getKey() + " has class " + p.getValue().getClass() +
                                ", but I expected " + allParameters.get(p) +
                                " (class " + allParameters.get(p).getType() + ")");
            }
            res += " " + p.getKey() + "='" + p.getValue() + "'";
            required.remove(p.getKey());
        }
        if (!required.isEmpty()) {
            throw new RuleException("Missing required arguments: " + required);
        }

        res += ";";
        if(pra.getBranchCount() > 1) {
            res += "\ncases {\n";
            for(BranchInfo bi : pra.getBranchInfo()) {
                res += "\tcase \"" + bi.getLabel() + "\": {\n\t\n\t}\n";
            }
            res += "}\n";
        }
        return res;
    }
}
