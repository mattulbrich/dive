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
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
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

    /**
     * Extracts parameters from a given termselector and a sequent.
     *
     * @param target the ProofNode the rule will be applied to
     * @param selection the sequent this rule will be applied on
     * @param selector a TermSelector pointing to the currently selected Term in the GUI
     * @return Parameters for the application of the rule
     * @throws RuleException
     */
    protected Parameters extractParameters(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Parameters params = new Parameters();
        if(selector != null) {
            Term on = selector.selectSubterm(selection);
            params.putValue("on", on);
        }
        return params;
    }

    /**
     * The concrete implementation of {@link #considerApplication(ProofNode, Parameters)} for each rule.
     *
     * @param target the ProofNode this rule is to be applied on
     * @param parameters the parameters for the rule application
     * @return the resulting ProofRuleApplication
     * @throws RuleException
     */
    protected abstract ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException;

    /**
     * Same as {@link #considerApplication(ProofNode, Sequent, TermSelector)} but for GUI convenience with different
     * parameters. To extract the actual parameters {@link #extractParameters(ProofNode, Sequent, TermSelector)} is
     * called. For a non standard parameter extraction override it.
     *
     * @param target    the proof node onto whose sequent the rule is to be applied.
     * @param selection a subsequent of the target's sequent. These are the
     *                  UI-selected top formulas.
     * @param selector  if a subformula has been selected, it is this selector that
     *                  represents it.
     * @return
     * @throws RuleException
     */
    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Parameters params = extractParameters(target, selection, selector);
        return considerApplication(target, params);
    }

    /**
     * considers the application of this rule. Returns a ProofRuleApplication which might be either applicable or
     * not applicable for the given parameters.
     *
     * @param target the ProofNode for which to consider the application of the rule
     * @param parameters the parameters for the rule application
     * @return the resulting application
     * @throws RuleException
     */
    public final ProofRuleApplication considerApplication(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication pra = considerApplicationImpl(target, parameters);
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(pra);
        if(pra.getApplicability() == ProofRuleApplication.Applicability.APPLICABLE && pra.getBranchCount() > 0) {
            builder.setTranscript(getTranscript(pra, parameters));
        }
        return builder.build();
    }

    /**
     * The concrete implementation of {@link #makeApplication(ProofNode, Parameters)} for each rule.
     *
     * @param target the ProofNode this rule is to be applied on
     * @param parameters the parameters for the rule application
     * @return the resulting ProofRuleApplication
     * @throws RuleException
     */
    protected abstract ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException;

    /**
     * Creates a ProofRuleApplication encoding all changes made by the rule when applied with given parameters to a
     * certain ProofNode.
     *
     * @param target
     *            the proof node onto whose sequent the rule is to be applied.
     * @param parameters
     *            the parameters as parsed from the proof script.
     * @return the ProofRuleApplication
     * @throws RuleException
     */
    public final ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);
        ProofRuleApplication pra = makeApplicationImpl(target, parameters);
        String transcript = getTranscript(pra, parameters);
        return new ProofRuleApplicationBuilder(pra).setTranscript(transcript).build();
    }

    /**
     * Creates a ProofRuleApplication conforming with the given parameters for a given sequent.
     *
     * @param params the parameters
     * @param s the sequent
     * @return the new application
     * @throws RuleException
     */
    protected ProofRuleApplicationBuilder handleControlParameters(Parameters params, Sequent s) throws RuleException {
        ProofRuleApplicationBuilder rab = new ProofRuleApplicationBuilder(this);
        return handleControlParameters(params, s, rab);
    }

    /**
     * This method sets the appropriate control parameters of a ProofRuleApplication builder for the given parameters.
     *
     * @param params the given parameters
     * @param s the sequent the application opperates on
     * @param rab the ProofRuleApplication to be updated according to the parameters
     * @return the updated application
     * @throws RuleException
     */
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

        if(allParameters.containsKey("on")) {
            Term t = params.getValue(ON_PARAM);
            Optional<TermSelector> ots = RuleUtil.matchSubtermInSequent(t::equals, s);
            if (ots.isPresent()) {
                rab.setOn(ots.get());
            }
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
        if(allParameters.size() == 0 && pra.getBranchCount() < 2) {
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
            if(allParameters.get(p.getKey()).getType().equals(ParameterType.TERM)) {
                PrettyPrint prettyPrint = new PrettyPrint();
                String pp = prettyPrint.print((Term)p.getValue()).toString();
                res += " " + p.getKey() + "='" + pp + "'";
            } else {
                res += " " + p.getKey() + "=\"" + p.getValue() + "\"";
            }
            required.remove(p.getKey());
        }
        if (!required.isEmpty()) {
            throw new RuleException("Missing required arguments: " + required);
        }

        res += ";";
        if(pra.getBranchCount() > 1) {
            res += "\ncases {\n";
            for(BranchInfo bi : pra.getBranchInfo()) {
                if(bi.getLabel() == null) {
                    throw new RuleException("Branchlabel may not be null for branching rule: " + getName());
                }
                res += "\tcase \"" + bi.getLabel() + "\": {\n\t\n\t}\n";
            }
            res += "}\n";
        }
        return res;
    }

    /**
     * This map captures the parameters made
     * known to the class in the constructor.
     */
    public Map<String, ParameterDescription<?>> getAllParameters() {
        return allParameters;
    }
}
