/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.term.FunctionSymbol;
import nonnull.NonNull;
import nonnull.Nullable;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Util;

/**
 * This is a builder (as in the builder pattern) for
 * {@link ProofRuleApplication}s.
 * <p>
 * All fields of the the rule application can be set using the according
 * methods.
 * <p>
 * {@link #notApplicable(ProofRule)} creates an objects indicating that the
 * rule is not applicable here.
 */
public class ProofRuleApplicationBuilder {

    /*
     * See the according fields of class ProofRuleApplication for
     * comparison
     */
    private final ProofRule rule;
    private final List<BranchInfoBuilder> branches = new ArrayList<>();
    private Applicability applicability = Applicability.APPLICABLE;
    private String scriptTranscript;
    private Parameters parameters = Parameters.EMPTY_PARAMETERS;
    private Parameters openParameters = Parameters.EMPTY_PARAMETERS;
    private Refiner refiner;

    private List<ProofRuleApplication> subApplications = null;
    private List<FunctionSymbol> newFuctionSymbols;

    /**
     * Instantiates a new proof rule application builder with a rule.
     * <p>
     * The transcript is initialised accordingly.
     *
     * @param rule the rule to be used.
     */
    public ProofRuleApplicationBuilder(@NonNull ProofRule rule) {
        this.rule = rule;
        this.scriptTranscript = rule.getName() + ";";
    }

    /**
     * Instantiates a new proof rule application builder from a rule.
     *
     * @param app the rule app whose fields are to be copied
     */
    public ProofRuleApplicationBuilder(ProofRuleApplication app) {
        this.rule = app.getRule();
        this.branches.addAll(Util.map(app.getBranchInfo(), x -> new BranchInfoBuilder(x)));
        this.applicability = app.getApplicability();
        this.parameters = app.getParameters();
        this.openParameters = app.getOpenParameters();
        this.refiner = app.getRefiner();
        if(app.getSubApplications() != null) {
            this.subApplications = new ArrayList<>(app.getSubApplications().asCollection());
        }
        if(app.getNewFunctionSymbols() != null) {
            this.newFuctionSymbols = new ArrayList<>(app.getNewFunctionSymbols().asCollection());
        }
    }

    /**
     * Create a new application indication "Not applicable".
     *
     * @param rule the rule to encapsulate
     * @return the proof rule application holding not-applicable for the rule
     */
    public static ProofRuleApplication notApplicable(ProofRule rule) {
        return new ProofRuleApplication(rule, BranchInfo.UNCHANGED,
                Applicability.NOT_APPLICABLE, Parameters.EMPTY_PARAMETERS, Parameters.EMPTY_PARAMETERS,
                null, null, null);
    }

    /**
     * Create a new instance with the set parameters.
     *
     * (see builder pattern)
     *
     * @return a freshly created proof rule application
     */
    public ProofRuleApplication build() {
        ImmutableList<BranchInfo> from = null;
        try {
            from = ImmutableList.from(Util.map(branches, BranchInfoBuilder::build));
        } catch (Exception ex){
            ex.printStackTrace();
            return null;
        }
        return new ProofRuleApplication(
                rule,
                from,
                applicability,
                parameters,
                openParameters,
                refiner,
                toListIfNotAllNull(subApplications),
                newFuctionSymbols == null ? null : ImmutableList.from(newFuctionSymbols));
    }

    /*
     * Create an immutable list from the argument if not all entries are null.
     * Return null if list is null, or only contains null entries.
     */
    private static <T> ImmutableList<T> toListIfNotAllNull(List<T> list) {
        if(list == null) {
            return null;
        }
        for (T t : list) {
            if(t != null) {
                return ImmutableList.from(list);
            }
        }
        return null;
    }

    public ProofRuleApplicationBuilder setApplicability(@NonNull Applicability applicable) {
        this.applicability = applicable;
        return this;
    }

    public ProofRuleApplicationBuilder setRefiner(@Nullable Refiner refiner) {
        this.refiner = refiner;
        return this;
    }

    public void setNewFuctionSymbols(List<FunctionSymbol> list) {
        this.newFuctionSymbols = list;
    }

    /**
     * Create and return a new branch builder.
     * The resulting branch has the given label.
     * <p>
     * The branch is built automatically from the child builder as soon as this
     * app is built.
     *
     * @param label the label to be used for the branch
     * @return the new branch info builder
     */
    public BranchInfoBuilder newBranch(@NonNull String label) {
        BranchInfoBuilder builder = new BranchInfoBuilder();
        builder.setLabel(label);
        branches.add(builder);
        return builder;
    }

    /**
     * Create and return a new branch builder.
     * The resulting branch is unlabeled.
     * <p>
     * The branch is built automatically from the child builder as soon as this
     * app is built.
     *
     * @return the new branch info builder
     */
    public BranchInfoBuilder newBranch() {
        return newBranch("");
    }


    /**
     * Sets this builder to "closing".
     *
     * This means there are no branches.
     *
     * @return <code>this</code>
     */
    public ProofRuleApplicationBuilder setClosing() {
        branches.clear();
        return this;
    }

    /**
     * Get a reference to the list of subapplications.
     *
     * This may be null!
     * The resulting list may be changed.
     *
     * @return a reference to a mutable list or null.
     */
    public List<ProofRuleApplication> getSubApplications() {
        return subApplications;
    }

    public ProofRuleApplicationBuilder setSubApplications(List<ProofRuleApplication> subApplications) {
        this.subApplications = subApplications;
        return this;
    }

    public ProofRuleApplicationBuilder setParameters(Parameters parameters) {
        this.parameters = parameters;
        return this;
    }

    public Parameters getParameters() {
        return parameters;
    }

}
