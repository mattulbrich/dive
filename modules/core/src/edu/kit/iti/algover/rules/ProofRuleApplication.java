/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;

import edu.kit.iti.algover.proof.ProofNode;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * This class captures potential applications of proof rules.
 *
 * They can be used to present possible next steps to the user or to actually
 * advance the proof state by applying them.
 *
 * This class does not directly handle applications. It's up to the applying
 * code to read out the {@link ProofRuleApplication#branchInfo} in order to
 * create children {@link ProofNode}s.
 *
 * Proof applications can be provisional (they might by applicable and might
 * not). To ultimately decide applicability, use the {@link #refine()} method
 * which returns a more concrete rule application.
 *
 * @param <E>
 *            the parameter type of the {@link ProofRule}
 *
 * @author mattias ulbrich
 */
public final class ProofRuleApplication<E> {

    /**
     * Applicability of a rule
     */
    public enum Applicability {

        /**
         * This rule application can be used directly.
         */
        APPLICABLE,

        /**
         * It has not been decided yet whether this rule application can
         * actually be used or not.
         */
        MAYBE_APPLICABLE,

        /**
         * The rule application cannot be applied. It does not match, does not
         * advance the state, etc.
         */
        NOT_APPLICABLE
    };

    /**
     * The rule to which this application belongs.
     */
    private final @NonNull ProofRule<E> rule;

    /**
     * The information about the branches into which this rule application
     * splits. Emtpy if closing rule app. Singleton list if the rule app does not
     * split etc.
     */
    private final @Nullable List<BranchInfo> branchInfo;

    /**
     * The applicability of this rule application.
     */
    private final @NonNull Applicability applicability;

    /**
     * The code which can be used to refine this proof application. Can be
     * <code>null</code> if no refining routine is known for this application.
     */
    private final @Nullable Supplier<ProofRuleApplication<E>> refiner;

    /**
     * When a proof rule application is applied, the proof script needs to be
     * augmented. This is the proof script transcript which describes this
     * application.
     */
    private final @NonNull String scriptTranscript;

    /**
     * Instantiates a new proof rule application.
     *
     * @param rule the rule to apply
     * @param branchInfo info about the branches to be created
     * @param applicability the applicability of this object.
     * @param scriptTranscript the script transcript
     * @param refiner the potential refiner
     */
    public ProofRuleApplication(
            @NonNull ProofRule<E> rule,
            @DeepNonNull List<BranchInfo> branchInfo,
            @NonNull Applicability applicability,
            @NonNull String scriptTranscript,
            @Nullable Supplier<ProofRuleApplication<E>> refiner) {
        this.rule = rule;
        this.branchInfo = branchInfo;
        this.applicability = applicability;
        this.refiner = refiner;
        this.scriptTranscript = scriptTranscript;
    }

    /**
     * Checks if this object is refinable, has got a refining procedure defined.
     *
     * @return <code>true</code> iff is refinable
     */
    public boolean isRefinable() {
        return refiner != null;
    }

    /**
     * Refine this {@link ProofRuleApplication} by returning a new element of
     * the same class.
     *
     * This method may return the very same object.
     *
     * <p>
     * Precondition: {@link #isRefinable()}
     *
     * @return the proof rule application after refinement.
     */
    public ProofRuleApplication<E> refine() {
        if(refiner == null) {
            return this;
        }

        ProofRuleApplication<E> result = refiner.get();

        if(result == null) {
            return thisWithoutRefiner();
        }

        return result;

    }

    private ProofRuleApplication<E> thisWithoutRefiner() {
        return new ProofRuleApplication<E>(rule, branchInfo, applicability, scriptTranscript, null);
    }

    /**
     * Returns the applicability of this rule application.
     *
     * If it is {@link Applicability#APPLICABLE applicable}, find out the number
     * of split branches using {@link #getBranchCount()}.
     *
     * @return the applicability
     */
    public @NonNull Applicability getApplicability() {
        return applicability;
    }

    /**
     * Gets the rule associated with this object.
     *
     * @return the rule
     */
    public ProofRule<E> getRule() {
        return rule;
    }

    /**
     * Gets the number of child branches this application has.
     *
     * @return a non-negative number
     */
    public int getBranchCount() {
        return branchInfo.size();
    }

    /**
     * Gets information about the branches this application would produce.
     *
     * @return an unmodifiable list of branch information
     */
    public List<BranchInfo> getBranchInfo() {
        return Collections.unmodifiableList(branchInfo);
    }

    /**
     * Gets the script transcript of this application.
     *
     * @return the script transcript
     */
    public String getScriptTranscript() {
        return scriptTranscript;
    }
}
