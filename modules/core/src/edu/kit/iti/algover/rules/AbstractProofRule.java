/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.beans.ParameterDescriptor;
import java.util.*;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;
import jdk.nashorn.internal.ir.BreakableNode;
import org.junit.Rule;

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
    public static final ParameterDescription<TermParameter> ON_PARAM =
            new ParameterDescription<>("on", ParameterType.TERM, true);

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
     * parameters.
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
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(selector, selection));
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
        if(builder.getParameters() == null) {
            builder.setParameters(parameters);
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
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(makeApplicationImpl(target, parameters));
        if(builder.getParameters() == null) {
            builder.setParameters(parameters);
        }
        return builder.build();
    }

    /**
     *
     * Generates a fitting transcript for a given ruleApplication.
     *
     * @param pra the proofRuleApplication
     * @return a valid transcript for the given proofRuleApplication
     * @throws RuleException
     */
    public String getTranscript(ProofRuleApplication pra) throws RuleException {
        Parameters params = pra.getParameters();
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
            if(allParameters.get(p.getKey()).getType().equals(ParameterType.TERM)) {
                PrettyPrint prettyPrint = new PrettyPrint();
                String pp = prettyPrint.print(((TermParameter) p.getValue()).getSchematicTerm()).toString();
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
                res += "\tcase match \"" + bi.getLabel() + "\": {\n\t\n\t}\n";
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
