/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.*;
import java.util.Map.Entry;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.Util;

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
            new ParameterDescription<>("on", ParameterType.MATCH_TERM, true);

    /**
     * The map internally storing all parameters.
     */
    private final Map<String, ParameterDescription<?>> allParameters;

    /**
     * Instantiate a new object.
     *
     * @param parameters a list of all parameters that this proof rule accepts.
     */
    public AbstractProofRule(ParameterDescription<?>... parameters) {
        allParameters = new LinkedHashMap<>();
        for (ParameterDescription<?> p : parameters) {
            allParameters.put(p.getName(), p);
        }
    }

    /**
     * {@inheritDoc}
     * <p>
     *     By default, the category of a class is Unknown
     *
     * @return "Unknown"
     */
    @Override
    public String getCategory() {
        return "Unknown";
    }

    /**
     * Check the actual parameters obtained as method parameter against the formal parameters stored
     * in {@link #allParameters},
     *
     * @param parameters the map of parameters against values.
     * @throws RuleException if a required parameter has been omitted or an unknown parameter has
     *                       been used
     */
    private void checkParameters(Parameters parameters) throws RuleException {
        Set<ParameterDescription<?>> required = new HashSet<>();
        for (ParameterDescription<?> p : allParameters.values()) {
            if(p.isRequired()) {
                required.add(p);
            }
        }

        for (Entry<ParameterDescription<?>, Object> en : parameters.entrySet()) {
            ParameterDescription<?> t = en.getKey();

            if (t == null) {
                throw new RuleException("Unknown parameter '" + en.getKey() + "'");
            }

            if(t.getType() == ParameterType.TERM) {
                if(((TermParameter)en.getValue()).getOriginalTermSelector() != null) {
                    // REVIEW: Why is this?
                    throw new RuleException("Term parameters may not be termSelectors.");
                }
            }

            Object value = en.getValue();
            if (!t.acceptsValue(value)) {
                throw new RuleException(
                        "\"" + value + "\" is not a valid value for parameter " +
                                en.getKey() + " (expected a " + t.getType() + ")");

            }

            required.remove(t);
        }

        if (!required.isEmpty()) {
                throw new RuleException("Missing required argument(s): " +
                        Util.commatize(required));
        }
    }

    /**
     * The concrete implementation of {@link #considerApplication(ProofNode, Parameters)} for each rule.
     *
     * @param target the ProofNode this rule is to be applied on
     * @param parameters the parameters for the rule application
     * @return the resulting ProofRuleApplication
     * @throws RuleException
     *
     * @deprecated Relict of old days
     */
    @Deprecated
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
        params.putValue(ON_PARAM, new TermParameter(selector, selection));
        try {
            ProofRuleApplication result = makeApplication(target, params);
            return result;
        } catch (NotApplicableException e) {
            throw e;
        }
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
        ProofRuleApplication app = makeApplicationImpl(target, parameters);
        if (app.getParameters().isEmpty()) {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(app);
            builder.setParameters(parameters);
            app = builder.build();
        }
        return app;
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
        PrettyPrint prettyPrint = new PrettyPrint();
        Parameters params = pra.getParameters();

        StringBuilder sb = new StringBuilder();

        List<String> args = new ArrayList<>();
        for(Entry<ParameterDescription<?>, Object> p : params.entrySet()) {
            String val = entryToString(p.getKey(), p.getValue(), prettyPrint);
            args.add(p.getKey().getName() + "=" + val);
        }

        sb.append(pra.getRule().getName());
        if(!args.isEmpty()) {
            sb.append(" ");
            sb.append(Util.join(args, " "));
        }
        sb.append(";");

        if(pra.getBranchCount() > 1) {
            sb.append("\ncases {\n");
            for(BranchInfo bi : pra.getBranchInfo()) {
                sb.append("\tcase match \"" + bi.getLabel() + "\": \n\n");
            }
            sb.append("}\n");
        }
        return sb.toString();
    }

    private <T> String entryToString(ParameterDescription<T> key,
                                 Object value,
                                 PrettyPrint prettyPrint) {
        T tvalue = key.castValue(value);
        return key.getType().prettyPrint(prettyPrint, tvalue);
    }

    /**
     * This map captures the parameters made
     * known to the class in the constructor.
     */
    @Override
    public Map<String, ParameterDescription<?>> getAllParameters() {
        return allParameters;
    }

    public boolean mayBeExhaustive() {
        return false;
    }
}
