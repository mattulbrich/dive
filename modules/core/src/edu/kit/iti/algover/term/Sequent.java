/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.List;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.TopFormula;
import edu.kit.iti.algover.util.Util;

public class Sequent {

    public Sequent(List<ProofFormula> ante, List<ProofFormula> succ) {
        this.antecedent = Util.toArray(ante, ProofFormula.class);
        this.succedent = Util.toArray(succ, ProofFormula.class);
    }

    private final ProofFormula antecedent[];

    private final ProofFormula succedent[];

    public List<ProofFormula> getAntecedent() {
        return Util.readOnlyArrayList(antecedent);
    }
}
