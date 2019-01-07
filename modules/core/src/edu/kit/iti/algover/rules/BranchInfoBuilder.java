/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.rules;

import java.util.ArrayList;
import java.util.List;

import nonnull.NonNull;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

/**
 * This is a builder (as in the builder pattern) for {@link BranchInfo}s.
 * <p>
 * All fields of the the rule application can be set using the according
 * methods.
 * <p>
 * {@link BranchInfoBuilder}s are usually constructed via the method
 * {@link ProofRuleApplicationBuilder#newBranch()} which connects this builder
 * automatically to the rule application builder
 *
 * @see BranchInfo
 * @see ProofRuleApplicationBuilder
 */
public class BranchInfoBuilder {

    private final List<ProofFormula> additionsAntecedent = new ArrayList<>();
    private final List<ProofFormula> additionsSuccedent = new ArrayList<>();

    private final List<ProofFormula> deletionsAntecedent = new ArrayList<>();
    private final List<ProofFormula> deletionsSuccedent = new ArrayList<>();

    private final List<Pair<TermSelector, Term>> replacements = new ArrayList<>();
    private String label;

    public BranchInfoBuilder(BranchInfo info) {
        additionsAntecedent.addAll(info.getAdditions().getAntecedent());
        additionsSuccedent.addAll(info.getAdditions().getSuccedent());
        deletionsAntecedent.addAll(info.getDeletions().getAntecedent());
        deletionsSuccedent.addAll(info.getDeletions().getSuccedent());
        replacements.addAll(info.getReplacements().asCollection());
        label = info.getLabel();
    }

    public BranchInfoBuilder() {
    }


    public BranchInfoBuilder addAdditionAntecedent(ProofFormula formula) {
        additionsAntecedent.add(formula);
        return this;
    }

    public BranchInfoBuilder addAdditionsSuccedent(ProofFormula proofFormula) {
        additionsSuccedent.add(proofFormula);
        return this;
    }

    public BranchInfoBuilder addReplacement(@NonNull TermSelector selector, @NonNull Term term) {
        replacements.add(new Pair<>(selector, term));
        return this;
    }

    public BranchInfo build() {
        Sequent additions = new Sequent(additionsAntecedent, additionsSuccedent);
        Sequent deletions = new Sequent(deletionsAntecedent, deletionsSuccedent);
        if (label == null) {
            throw new NullPointerException("Branch label is null");
        }

        return new BranchInfo(label, additions, deletions, ImmutableList.from(replacements));
    }

    public BranchInfoBuilder addAdditions(Sequent sequent) {
        additionsAntecedent.addAll(sequent.getAntecedent());
        additionsSuccedent.addAll(sequent.getSuccedent());
        return this;
    }

    public BranchInfoBuilder addDeletions(Sequent sequent) {
        deletionsAntecedent.addAll(sequent.getAntecedent());
        deletionsSuccedent.addAll(sequent.getSuccedent());
        return this;
    }

    public BranchInfoBuilder addDeletionsAntecedent(ProofFormula... deletionsAnte) {
        deletionsAntecedent.addAll(Util.readOnlyArrayList(deletionsAnte));
        return this;
    }

    public BranchInfoBuilder addDeletionsAntecedent(List<ProofFormula> deletionsAnte) {
        deletionsAntecedent.addAll(deletionsAnte);
        return this;
    }

    public BranchInfoBuilder addDeletionsSuccedent(ProofFormula... deletionsSucc) {
        addDeletionsSuccedent(Util.readOnlyArrayList(deletionsSucc));
        return this;
    }

    public BranchInfoBuilder addDeletionsSuccedent(List<ProofFormula> deletionsSucc) {
        deletionsSuccedent.addAll(deletionsSucc);
        return this;
    }

    public String getLabel() {
        return label;
    }

    public BranchInfoBuilder setLabel(String label) {
        this.label = label;
        return  this;
    }

}
