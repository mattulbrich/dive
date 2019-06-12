/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.*;
import java.util.Map.Entry;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.ExcusableValue;
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
     *     By default, the category of a rule is "Unknown"
     *
     * @return "Unknown"
     */
    @Override
    public String getCategory() {
        return "Unknown";
    }

    /**
     * Check the actual parameters obtained as method parameter against the
     * formal parameters stored in {@link #allParameters},
     *
     * @param parameters the map of parameters against values.
     * @return {@code null} if the parameters are ok with the rule's
     * requirements. A non-{@code null} string indicates an error message if the
     * the parameters are against the rule's requirements. Can be used for an
     * exception message or a rgret message.
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
     * The concrete implementation of considerApplication(ProofNode, Parameters) for each rule.
     *
     * @param target the ProofNode this rule is to be applied on
     * @param parameters the parameters for the rule application
     * @return the resulting ProofRuleApplication
     * @throws RuleException
     *
     * @deprecated A relict of old days
     */
    @Deprecated
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        throw new Error("Will be removed");
    }

    @Deprecated
    public final ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Parameters params = new Parameters();
        params.putValue(ON_PARAM, new TermParameter(selector, selection));
        return makeApplicationImpl_OLD(target, params);
    }


    /**
     * The concrete implementation of {@link #makeApplication(ProofNode, Parameters)} for each rule.
     *
     * @param target the ProofNode this rule is to be applied on
     * @param parameters the parameters for the rule application
     * @return the resulting ProofRuleApplication
     * @throws RuleException
     */
    // protected abstract ExcusableValue<ProofRuleApplication> makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException;
    protected ExcusableValue<ProofRuleApplication, RuleException> makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        // This method will be abstract in the future.
        // For now it calls to the old methods before the refactoring.
        System.err.println("This is legacy code that must be adapted!");
        return ExcusableValue.value(makeApplicationImpl_OLD(target, parameters));
    };

    /**
     * @deprecated This is a relict of old days
     */
    @Deprecated
    protected ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        throw new Error("Will be removed");
    }

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
    public final ExcusableValue<ProofRuleApplication, RuleException> makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        try {
            checkParameters(parameters);
        } catch(RuleException ex) {
            return ExcusableValue.excuse(ex);
        }

        ExcusableValue<ProofRuleApplication, RuleException> result = makeApplicationImpl(target, parameters);

        result = result.map(pra ->
            pra.getParameters().isEmpty() ?
                new ProofRuleApplicationBuilder(pra)
                        .setParameters(parameters).build() :
                    pra);

        return result;
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

    protected static ExcusableValue<ProofRuleApplication, RuleException> regret(String msg) {
        return ExcusableValue.excuse(new RuleException(msg));
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
        return Collections.unmodifiableMap(allParameters);
    }

    public boolean mayBeExhaustive() {
        return false;
    }
}
