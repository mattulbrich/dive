package edu.kit.iti.algover.rules;

import java.util.ArrayList;
import java.util.List;

import nonnull.NonNull;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

public class BranchInfoBuilder {

    private final List<ProofFormula> additionsAntecedent = new ArrayList<>();
    private final List<ProofFormula> additionsSuccedent = new ArrayList<>();

    private final List<ProofFormula> deletionsAntecedent = new ArrayList<>();
    private final List<ProofFormula> deletionsSuccedent = new ArrayList<>();

    private final List<Pair<TermSelector, Term>> replacements = new ArrayList<>();

    public BranchInfoBuilder(BranchInfo info) {

    }

    public BranchInfoBuilder() {
        // TODO Auto-generated constructor stub
    }


    public BranchInfoBuilder addAdditionAntecedent(ProofFormula formula) {
        additionsAntecedent.add(formula);
        return this;
    }

    public BranchInfoBuilder addReplacement(@NonNull TermSelector selector, @NonNull Term term) {
        replacements.add(new Pair<>(selector, term));
        return this;
    }

    public BranchInfo build() {
        // FIXME
        return new BranchInfo(null, null, null);
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

    public BranchInfoBuilder addDeletionsAntecedent(List<ProofFormula> deletionsAnte) {
        deletionsAntecedent.addAll(deletionsAnte);
        return this;
    }

    public BranchInfoBuilder addDeletionsSuccedent(List<ProofFormula> deletionsSucc) {
        deletionsSuccedent.addAll(deletionsSucc);
        return this;
    }

}
