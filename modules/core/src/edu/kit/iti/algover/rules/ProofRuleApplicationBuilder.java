/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.ArrayList;
import java.util.List;

public class ProofRuleApplicationBuilder {

    private ProofRule rule;
    private List<BranchInfo> branches = new ArrayList<>();
    private Applicability applicability = Applicability.APPLICABLE;
    private String scriptTranscript;
    private Parameters openParameters = Parameters.EMPTY_PARAMETERS;
    private Refiner refiner;

    public ProofRuleApplicationBuilder(@NonNull ProofRule rule) {
        this.rule = rule;
        this.scriptTranscript = rule.getName();
    }

    public ProofRuleApplicationBuilder(ProofRuleApplication app) {
        this.rule = app.getRule();
        this.branches.addAll(app.getBranchInfo().asCollection());
        this.applicability = app.getApplicability();
        this.scriptTranscript = app.getScriptTranscript();
        this.openParameters = app.getOpenParameters();
        this.refiner = app.getRefiner();
    }

    public static ProofRuleApplication notApplicable(ProofRule rule) {
        return new ProofRuleApplication(rule, BranchInfo.UNCHANGED,
                Applicability.NOT_APPLICABLE, rule.getName(),
                Parameters.EMPTY_PARAMETERS, null);
    }

    public ProofRuleApplication build() {
        return new ProofRuleApplication(
                rule,
                ImmutableList.from(branches),
                applicability,
                scriptTranscript,
                openParameters,
                refiner);
    }

    public ProofRuleApplicationBuilder addReplacementBranch(@NonNull TermSelector selector, @NonNull Term term) {
        BranchInfo info = new BranchInfo(Sequent.EMPTY, Sequent.EMPTY,
                ImmutableList.single(new Pair<>(selector, term)));
        branches.add(info);
        return this;
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

    public ProofRuleApplicationBuilder setClosing() {
        branches.clear();
        return this;
    }

}
