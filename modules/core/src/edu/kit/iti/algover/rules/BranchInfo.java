/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import nonnull.DeepNonNull;
import nonnull.NonNull;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

/**
 * BranchInfos capture the information to obtain new {@link ProofNode}s during
 * {@link ProofRuleApplication}s.
 *
 * All information that belongs to the branch is kept here while general
 * information shared by branches is kept in {@link ProofRuleApplication}.
 *
 * @author mattias ulbrich
 *
 */
public class BranchInfo {

    /**
     * The special case of a single branch which does not change anything.
     */
    public static final ImmutableList<BranchInfo> UNCHANGED =
            ImmutableList.single(
                    new BranchInfo("", Sequent.EMPTY, Sequent.EMPTY, ImmutableList.nil()));

    /**
     * The special case of a closing rule with no branches.
     */
    public static final ImmutableList<BranchInfo> CLOSE =
            ImmutableList.nil();

    /**
     * The additions to the sequent.
     */
    private final @NonNull Sequent additions;

    /**
     * The deletions from the sequent.
     */
    private final @NonNull Sequent deletions;

    /**
     * The replacements.
     */
    private final @DeepNonNull ImmutableList<Pair<TermSelector, Term>> replacements;

    private final String label;

    /**
     * Instantiates a new branch info.
     *
     * @param label
     *            the label associated to this branch
     * @param additions
     *            the toplevel terms to be added to the node's sequent
     * @param deletions
     *            the toplevel terms to be removed from the node's sequent
     * @param replacements
     *            the terms to be replaced
     */
    public BranchInfo(@NonNull String label,
            @NonNull Sequent additions,
            @NonNull Sequent deletions,
            @DeepNonNull ImmutableList<Pair<TermSelector, Term>> replacements) {
        this.label = label;
        this.additions = additions;
        this.deletions = deletions;
        this.replacements = replacements;
    }

    /**
     * Instantiates a new branch info with empty additions and deletion
     * sequences.
     *
     * The replacements are cosntructed from the arguments.
     *
     * @param replacements
     *            the term replacements to be used.
     * @return a freshly created object
     */
    @SafeVarargs
    public static BranchInfo makeReplacement(Pair<TermSelector, Term>... replacements) {
        return new BranchInfo("", Sequent.EMPTY, Sequent.EMPTY,
                ImmutableList.<Pair<TermSelector, Term>>from(replacements));
    }

    /**
     * Gets the additions to the sequent
     *
     * @return the additions as a sequent
     */
    public @NonNull Sequent getAdditions() {
        return additions;
    }

    /**
     * Gets the deletions from the sequent.
     *
     * @return the deletions as sequent
     */
    public @NonNull Sequent getDeletions() {
        return deletions;
    }

    /**
     * Gets the replacements within the sequent.
     *
     * @return an unmodifiable list of term replacements.
     */
    public @DeepNonNull ImmutableList<Pair<TermSelector, Term>> getReplacements() {
        return replacements;
    }

    /**
     * Gets the branch label associated to this branch
     *
     * @return the label
     */
    public @NonNull String getLabel() {
        return label;
    }

}
