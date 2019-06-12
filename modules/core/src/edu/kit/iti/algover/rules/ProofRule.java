/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.ExcusableValue;
import nonnull.NonNull;

import java.util.Map;

/**
 * Interface for Proof steps Proof steps can be single rules, but also
 * application of solvers etc.
 *
 * A proof rule may take parameters. The concrete class which is responsible for
 * taking parameters for a particular rule is captured in a type parameter.
 *
 * @author Mattias Ulbrich
 */
public interface ProofRule {

    /**
     * Gets the name of this proof rule.
     * <p>
     * This name is also the command under which it is accessible in scripts.
     *
     * @return a string which matches <code>[A-Za-z][A-Za-z0-9_]*</code>.
     */
    public @NonNull String getName();

    /**
     * Gets the category to which this proof rule belongs.
     * <p>
     * The number of supported categories may grow over time
     *
     * @return a string describing the category of this rule. Must not change
     * from call to call. It matches <code>[A-Za-z ]+</code>
     */
    public @NonNull String getCategory();

    /**
     * Create a {@link ProofRuleApplication} for a proof node and a parameter
     * object.
     * <p>
     * This method can be invoked  from a user interaction context or from a
     * scripting context. Its results are to be interpreted accordingly.
     *
     * The result is a {@link ExcusableValue grettable value} that eiher
     * contains a {@link ProofRuleApplication} for a (possibly applicable)
     * situation or does not. Then the excuse message returns a reason why the
     * rule cannot be applied.
     *
     * The resulting application may be {@link ProofRuleApplication#refine()
     * refinable} and may still have uninstantiated variables and thus not be
     * directly applicable.
     *
     * Any {@link ProofRuleApplication#getApplicability() applicability value}
     * is possible for the result..
     *
     * Missing/wrong parameters should not raise an exception.
     *
     * @param target     the proof node onto whose sequent the rule is to be
     *                   applied.
     * @param parameters the parameters for the rule.
     * @return a regrettable proof rule application that matches the selected
     * target with the given parameters. This is not necessarily applicable. If
     * it is known to be not applicable, a excuse string is returned explaining
     * the reason.
     * @throws RuleException if something unexpected happens during creation. If
     *                       a rule is not applicable, no exception should be
     *                       raised.
     */
    public @NonNull ExcusableValue<ProofRuleApplication, RuleException> makeApplication(
            @NonNull ProofNode target,
            @NonNull Parameters parameters) throws RuleException;


    /**
     * @deprecated Will be removed soon!
     */
    @Deprecated
    ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException;

    /**
     * Returns a map that captures the available rule parameters.
     *
     * @return an immutable map.
     */
    public Map<String, ParameterDescription<?>> getAllParameters();

    /**
     *
     * Generates a fitting transcript for a given ruleApplication.
     *
     * @param pra the proofRuleApplication
     * @return a valid transcript for the given proofRuleApplication
     * @throws RuleException
     */
    public String getTranscript(ProofRuleApplication pra) throws RuleException;

    /**
     * Describes whether this rule may be applied exhaustively or not
     *
     * @return true if this rule is exhaustively applicable. Must not change from
     * call to call.
     */
    public boolean mayBeExhaustive();
}
