/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import com.google.common.base.Objects;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import nonnull.DeepNonNull;
import nonnull.NonNull;

import java.util.Arrays;
import java.util.Collections;

/**
 * This class represents a single formula in the sequent
 *
 * Proof formulas can have labels which are arbitrary strings.
 * As far as the proof formula is concerned, no semantics is given to the labels.
 *
 * They contribute to equality of proof formulas, however.
 */
public class ProofFormula {

    /**
     * The actual term which is captured in this object.
     */
    private final @NonNull Term formula;

    /**
     * A proof formula may be tagged with labels
     */
    private final @DeepNonNull
    ImmutableList<String> labels;


    public ProofFormula(Term formula, Iterable<String> labels) {
        this.formula = formula;
        this.labels = ImmutableList.from(labels);
        // TODO. Activate this assertion once test cases are fixed.
        // assert formula.getSort().isSubtypeOf(Sort.BOOL);
    }

    public ProofFormula(Term formula, String... labels) {
        this(formula, Arrays.asList(labels));
    }

    public ProofFormula(Term formula) {
        this(formula, Collections.emptyList());
    }

    /**
     * Gets the term representing the proof formula.
     *
     * @return a formula of sort {@link Sort#BOOL}.
     */
    public @NonNull Term getTerm() {
        return this.formula;
    }

    /**
     * Gets the labels attached to the proof formula.
     *
     * @return non-null list of labels.
     */
    public @DeepNonNull ImmutableList<String> getLabels() {
        return labels;
    }

    @Override
    public String toString(){

        if (labels.isEmpty()) {
            return formula.toString();
        } else {
            return "[" + labels + "]: " + formula.toString();
        }
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(labels, formula);
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ProofFormula) {
            ProofFormula other = (ProofFormula) obj;
            return labels.equals(other.labels) && formula.equals(other.formula);
        }
        return false;
    }
}
