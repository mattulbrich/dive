/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.util.Util;

import java.util.List;

/**
 * Class representing a logical sequent
 */
public class Sequent {

    private final ProofFormula antecedent[];
    private final ProofFormula succedent[];

    public Sequent(List<ProofFormula> ante, List<ProofFormula> succ) {
        this.antecedent = Util.toArray(ante, ProofFormula.class);
        this.succedent = Util.toArray(succ, ProofFormula.class);
    }

    public List<ProofFormula> getAntecedent() {
        return Util.readOnlyArrayList(antecedent);
    }

    public List<ProofFormula> getSuccedent() {
        return Util.readOnlyArrayList(succedent);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(getAntecedent().toString());
        sb.append(" ==> ");
        sb.append(getSuccedent().toString());

        return sb.toString();
    }
}
