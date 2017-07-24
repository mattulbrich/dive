/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;

import nonnull.NonNull;
import nonnull.Nullable;

public final class ProofRuleApplication<E> {

    public enum Applicability {
        APPLICABLE, MAYBE_APPLICABLE, NOT_APPLICABLE
    };

    private final @NonNull ProofRule<E> rule;
    private final @Nullable List<ChangeInfo> changeInfo;
    private final @NonNull Applicability applicability;
    private final @Nullable Supplier<ProofRuleApplication<E>> refiner;
    private final @NonNull String scriptTranscript;

    public ProofRuleApplication(ProofRule<E> rule,
            List<ChangeInfo> changeInfo,
            Applicability applicability,
            String scriptTranscript,
            Supplier<ProofRuleApplication<E>> refiner) {
        this.rule = rule;
        this.changeInfo = changeInfo;
        this.applicability = applicability;
        this.refiner = refiner;
        this.scriptTranscript = scriptTranscript;
    }

    public boolean isRefinable() {
        return refiner != null;
    }

    public ProofRuleApplication<E> refine() {
        if(refiner == null) {
            return this;
        }

        return refiner.get();
    }

    public @NonNull Applicability getApplicability() {
        return applicability;
    }

    public ProofRule<E> getRule() {
        return rule;
    }

    public int getBranchCount() {
        return changeInfo.size();
    }

    public List<ChangeInfo> getChangeInfo() {
        return Collections.unmodifiableList(changeInfo);
    }

    public String getScriptTranscript() {
        return scriptTranscript;
    }
}
