/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.Sequent;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * Interface for Proof steps Proof steps can be single rules, but also
 * application of solvers etc.
 *
 * A proof rule may take parameters. The concrete class which is responsible for
 * taking parameters for a particular rule is captured in a type parameter.
 *
 * @author mulbrich
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
     * Create a {@link ProofRuleApplication} from a user interaction context.
     * <p>
     * The resulting application may be {@link ProofRuleApplication#refine()
     * refinable} and may still have uninstantiated variables and thus not be
     * applicable.
     *
     * @param target    the proof node onto whose sequent the rule is to be applied.
     * @param selection a subsequent of the target's sequent. These are the
     *                  UI-selected top formulas.
     * @param selector  if a subformula has been selected, it is this selector that
     *                  represents it.
     * @return the proof rule application that matches the selected target with
     * the given parameters. May be {@link Applicability#NOT_APPLICABLE
     * not applicable}.
     * @throws RuleException if something is unexpected during creation. If a rule is not
     *                       applicable, no exception should be raised.
     */
    public ProofRuleApplication considerApplication(
            @NonNull ProofNode target,
            @NonNull Sequent selection,
            @Nullable TermSelector selector) throws RuleException;


    /**
     * Create a {@link ProofRuleApplication} from a scripting context.
     * <p>
     * The parameters have to be passed as a parameters object.
     *
     * @param target     the proof node onto whose sequent the rule is to be applied.
     * @param parameters the parameters as parsed from the proof script.
     * @return the proof rule application that matches the selected target with
     * the given parameters. May be {@link Applicability#NOT_APPLICABLE
     * not applicable}.
     * @throws RuleException if something is unexpected during creation. If a rule is not
     *                       applicable, no exception should be raised.
     *                       Missing/wrong/illtyped parameters should also throw an
     *                       exception.
     */
    public ProofRuleApplication makeApplication(
            @NonNull ProofNode target,
            @NonNull Parameters parameters) throws RuleException;

}