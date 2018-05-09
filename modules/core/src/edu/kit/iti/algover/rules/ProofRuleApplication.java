/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.util.ImmutableList;
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
 * @author mattias ulbrich
 */
public final class ProofRuleApplication {

        /**
     * The rule to which this application belongs.
     */
        private final
        @NonNull
        ProofRule rule;
    ;
    /**
     * The information about the branches into which this rule application
     * splits. Emtpy if closing rule app. Singleton list if the rule app does not
     * split etc.
     */
    private final
    @Nullable
    ImmutableList<BranchInfo> branchInfo;
    /**
     * The applicability of this rule application.
     */
    private final @NonNull Applicability applicability;
    /**
     * Missing parameters. All parameters contained in this object require
     * instantiation for the application of the rule to be possible. The
     * parameters here are set immutable.
     */
    private final
    @NonNull
    Parameters openParameters;

    /**
     * The code which can be used to refine this proof application. Can be
     * <code>null</code> if no refining routine is known for this application.
     */
    private final
    @Nullable
    Refiner refiner;

    /**
     * When a proof rule application is applied, the proof script needs to be
     * augmented. This is the proof script transcript which describes this
     * application.
     */
    private final @NonNull String scriptTranscript;

    /**
     * A rule may be applied exhaustively meaning that it is recursively applied to the term resulting from the
     * previous application as long as possible. This parameter describes whether or not the rule application
     * is exhaustive or not.
     */
    private final boolean exhaustive;

    /**
     * Similar to exhaustive rule applications a rule might be applied deep exhaustive. In this case the recursive
     * applications continue even if there is a term where the rule is not applicable (in this case it is applied to
     * all child-terms).
     */
    private final boolean deep;

    /**
     * A rule might be applied globally meaning it is not only applied to 1 specific term but to all proofformulas
     * in the sequent. This may be combined with exhaustive or deep exhaustive applications.
     */
    private final boolean global;

    /**
     * This TermSelector points to the term this rule is going to be applied on.
     */
    private final TermSelector on;

    /**
     * Instantiates a new proof rule application.
     *
     * The passed parameters object is set to immutable.
     *
     * @param rule
     *            the rule to apply
     * @param branchInfo
     *            info about the branches to be created
     * @param applicability
     *            the applicability of this object.
     * @param scriptTranscript
     *            the script transcript
     * @param openParameters
     *            parameters that are missing for this application to be
     *            executed (use {@link Parameters#EMPTY_PARAMETERS} if no
     *            such parameters exist.
     * @param refiner
     *            the potential refiner
     * @param exhaustive
     *            whether the rule should be applied exhaustive
     * @param deep
     *            whether the rule should be applied deep exhaustive
     * @param deep
     *            whether the rule should be applied global
     * @param on
     *            pointing to the Term this application is applied to
     */
    public ProofRuleApplication(
            @NonNull ProofRule rule,
            @DeepNonNull ImmutableList<BranchInfo> branchInfo,
            @NonNull Applicability applicability,
            @NonNull String scriptTranscript,
            @NonNull Parameters openParameters,
            @Nullable Refiner refiner,
            @NonNull boolean exhaustive,
            @NonNull boolean deep,
            @NonNull boolean global,
            @Nullable TermSelector on) {
        this.rule = rule;
        this.branchInfo = branchInfo;
        this.applicability = applicability;
        this.refiner = refiner;
        this.openParameters = openParameters;
        this.scriptTranscript = scriptTranscript;
        openParameters.setImmutable();
        this.exhaustive = exhaustive;
        this.deep = deep;
        this.global = global;
        this.on = on;
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
     *
     * @throws RuleException
     *             if the the refinement process fails
     *
     * @see #refine(Parameters)
     */
    public ProofRuleApplication refine() throws RuleException {
        return refine(Parameters.EMPTY_PARAMETERS);
    }

    /**
     * Refine this {@link ProofRuleApplication} by returning a new element of
     * the same class.
     * <p>
     * This method may return the very same object.
     * <p>
     * <p>
     * This version of the refinement method takes {@link Parameters} as
     * argument. This is in particular needed if a rule application is marked
     * {@link Applicability#INSTANTIATION_REQUIRED}. The instantiation is the
     * to be provided using the parameters. Other use cases are possible.
     * <p>
     * <p>
     * Precondition: {@link #isRefinable()}
     *
     * @return the proof rule application after refinement.
     * @throws RuleException if the the refinement process fails
     * @see #refine()
     */
    private ProofRuleApplication refine(@NonNull Parameters parameters) throws RuleException {
        if(refiner == null) {
            return this;
        }

        ProofRuleApplication result = refiner.refine(this, parameters);

        if (result == null) {
            return thisWithoutRefiner();
        }

        return result;

    }

    /*
     * create a copy of this object with the "refiner" field set to
     * <code>null</code>.
     */
    private ProofRuleApplication thisWithoutRefiner() {
        return new ProofRuleApplication(rule, branchInfo, applicability,
                scriptTranscript, openParameters, null, exhaustive, deep, global, on);
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
    public ProofRule getRule() {
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
    public ImmutableList<BranchInfo> getBranchInfo() {
        return branchInfo;
    }


    /**
     * checks if this application is exhaustive.
     * @return if its exhaustive
     */
    public boolean isExhaustive() {
        return exhaustive;
    }

    /**
     * checks if this application is deep.
     * @return if its deep
     */
    public boolean isDeep() {
        return deep;
    }

    /**
     * checks if this application is global.
     * @return if its global
     */
    public boolean isGlobal() {
        return global;
    }

    /**
     * Gets the termSelector for the on parameter
     * @return the termselector
     */
    public TermSelector getOn() {
        return on;
    }

    /**
     * Gets the script transcript of this application.
     *
     * @return the string for the script transcript
     */
    public
    @NonNull
    String getScriptTranscript() {
        return scriptTranscript;
    }

    /**
     * Gets the parameters which were declared as remaining open.
     *
     * @return the open parameters
     */
    public
    @NonNull
    Parameters getOpenParameters() {
        return openParameters;
    }

    /**
     * Gets the refining code which may add information to the proof app by
     * returning a new one.
     *
     * @return the refiner, <code>null</code> if none set!
     */
    public @Nullable
    Refiner getRefiner() {
        return refiner;
    }

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
         * The rule application can definitely not be applied. It does not
         * match, does not advance the state, etc.
         */
        NOT_APPLICABLE,

        /**
         * The rule cannot yet be applied. Some schema variables need
         * instantiation.
         */
        INSTANTIATION_REQUIRED,
    }
}
