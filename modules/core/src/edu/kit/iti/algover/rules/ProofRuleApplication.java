/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.util.ImmutableList;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static edu.kit.iti.algover.util.ImmutableList.from;
import static edu.kit.iti.algover.util.ImmutableList.nil;

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
    private final @NonNull ProofRule rule;

    /**
     * Possible "SubApplications"
     * If not null, these ProofRuleApplications are performed on the
     * resulting childNodes of this ProofRuleApplication.
     *
     * May contain null-entries if no rule is to be applied on a child node.
     *
     * Invariant: <code>
     *   subApplications != null ==> subApplications.size() == branchInfo.size()
     * </code>
     */
    private final ImmutableList<ProofRuleApplication> subApplications;

    /**
     * The information about the branches into which this rule application
     * splits. Emtpy if closing rule app. Singleton list if the rule app does not
     * split etc.
     */
    private final @Nullable ImmutableList<BranchInfo> branchInfo;

    /**
     * The applicability of this rule application.
     */
    private final @NonNull Applicability applicability;

    /**
     * Parameters for this application. All parameters contained in this object require
     * instantiation for the application of the rule to be possible. The
     * parameters here are set immutable.
     */
    private final @NonNull Parameters parameters;

    /**
     * The code which can be used to refine this proof application. Can be
     * <code>null</code> if no refining routine is known for this application.
     */
    private final @Nullable Refiner refiner;

    /**
     * New function symbols introduced by this ruleApplication. These get added to the PVCs FunctionSymbols
     * if the application gets applied.
     */
    private final ImmutableList<FunctionSymbol> newFunctionSymbols;

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
     * @param refiner
     *            the potential refiner
     * @param subApplications
     *            possible SubApplications which are performed on the children
     *            resulting from this application (see {@link ProofRuleApplication#subApplications})
     */
    public ProofRuleApplication(
            @NonNull ProofRule rule,
            @DeepNonNull ImmutableList<BranchInfo> branchInfo,
            @NonNull Applicability applicability,
            @NonNull Parameters parameters,
            @Nullable Refiner refiner,
            @Nullable ImmutableList<ProofRuleApplication> subApplications,
            @Nullable ImmutableList<FunctionSymbol> newFunctionsymbols) {
        this.rule = rule;
        this.branchInfo = branchInfo;
        this.applicability = applicability;
        this.refiner = refiner;
        this.parameters = parameters;
        parameters.setImmutable();
        this.subApplications = subApplications;
        if (newFunctionsymbols != null) {
            this.newFunctionSymbols = newFunctionsymbols;
        } else {
            this.newFunctionSymbols = ImmutableList.nil();
        }

        if(subApplications != null && subApplications.size() != branchInfo.size()) {
            throw new IllegalArgumentException(
                    "number of sub applications does not match number of branches");
        }
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
        return new ProofRuleApplication(rule, branchInfo, applicability, parameters,
                null, subApplications, newFunctionSymbols);
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
     * Gets the parameters which were declared as remaining open.
     *
     * This means: Return those parameters which are parameters of the rule
     * but not set in the parameters object returned by {@link #getParameters()}.
     *
     * Optional and mandatory parameters are both collected.
     *
     * @return a freshly created collection of parameters that are not specified
     */
    public @NonNull Collection<ParameterDescription<?>> getOpenParameters() {
        List<ParameterDescription<?>> result = new ArrayList<>();
        for (ParameterDescription<?> pd : getRule().getAllParameters().values()) {
            if (!parameters.hasValue(pd)) {
                result.add(pd);
            }
        }
        return result;
    }

    /**
     * Gets the parameters which are used for this application.
     *
     * @return the parameters
     */
    public @NonNull Parameters getParameters() {
        return parameters;
    }

    /**
     * Gets the followup rule applications to apply on branches.
     *
     * May return null!
     *
     * If not null, these ProofRuleApplications are to be performed on the
     * resulting childNodes of this ProofRuleApplication.
     *
     * May contain null-entries if no rule is to be applied on a child node.
     *
     * Invariant: <code>
     *   \result != null ==> \result.size() == getBranchCount()
     * </code>
     */
    public @Nullable ImmutableList<ProofRuleApplication> getSubApplications() {
        return subApplications;
    }

    /**
     * Gets the refining code which may add information to the proof app by
     * returning a new one.
     *
     * @return the refiner, <code>null</code> if none set!
     */
    public @Nullable Refiner getRefiner() {
        return refiner;
    }

    /**
     *
     * Generates a valid transcript for this ruleApplication.
     *
     * A transcript is considered valid if interpreted an equivalent ProofRuleApplication
     * would be created.
     *
     * @return a valid transcript for this proofRuleApplication
     * @throws RuleException
     */
    public String getScriptTranscript() throws RuleException {
        return this.getRule().getTranscript(this);
    }

    public ImmutableList<FunctionSymbol> getNewFunctionSymbols() {
        return newFunctionSymbols;
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
