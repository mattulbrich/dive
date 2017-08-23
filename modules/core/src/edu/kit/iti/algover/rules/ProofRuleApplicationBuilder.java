/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.ArrayList;
import java.util.List;

import nonnull.NonNull;
import nonnull.Nullable;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

/**
 * This is a builder (as in the builder pattern) for
 * {@link ProofRuleApplication}s.
 *
 * All fields of the the rule application can be set using the according
 * methods.
 *
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
    private Parameters openParameters = Parameters.EMPTY_PARAMETERS;
    private Refiner refiner;

    /**
     * Instantiates a new proof rule application builder with a rule.
     *
     * The transcript is initialised accordingly.
     *
     * @param rule the rule to be used.
     */
    public ProofRuleApplicationBuilder(@NonNull ProofRule rule) {
        this.rule = rule;
        this.scriptTranscript = rule.getName();
    }

    /**
     * Instantiates a new proof rule application builder from a rule.
     *
     * @param app the rule app whose fields are to be copied
     */
    public ProofRuleApplicationBuilder(ProofRuleApplication app) {
        this.rule = app.getRule();
        this.branches.addAll(Util.map(app.getBranchInfo(), x-> new BranchInfoBuilder(x)));
        this.applicability = app.getApplicability();
        this.scriptTranscript = app.getScriptTranscript();
        this.openParameters = app.getOpenParameters();
        this.refiner = app.getRefiner();
    }

    /**
     * Create a new instance with the set parameters.
     *
     * (see builder pattern)
     *
     * @return a freshly created proof rule application
     */
    public ProofRuleApplication build() {
        return new ProofRuleApplication(
                rule,
                ImmutableList.from(Util.map(branches, BranchInfoBuilder::build)),
                applicability,
                scriptTranscript,
                openParameters,
                refiner);
    }

    public BranchInfoBuilder newBranch() {
        BranchInfoBuilder builder = new BranchInfoBuilder();
        branches.add(builder);
        return builder;
    }

    public ProofRuleApplicationBuilder setApplicability(@NonNull Applicability applicable) {
        this.applicability = applicable;
        return this;
    }

    public ProofRuleApplicationBuilder setTranscript(@NonNull String string) {
        this.scriptTranscript = string;
        return this;
    }

    public ProofRuleApplicationBuilder setRefiner(@Nullable Refiner refiner) {
        this.refiner = refiner;
        return this;
    }

    /**
     * Create a new application indication "Not applicable".
     *
     * @param rule
     *            the rule to encapsulate
     * @return the proof rule application holding not-applicable for the rule
     */
    public static ProofRuleApplication notApplicable(ProofRule rule) {
        return new ProofRuleApplication(rule, BranchInfo.UNCHANGED,
                Applicability.NOT_APPLICABLE, rule.getName(),
                Parameters.EMPTY_PARAMETERS, null);
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

}
