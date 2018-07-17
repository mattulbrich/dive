/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;


/**
 * Class representing a logical sequent
 */
public final class Sequent {

    public static final Sequent EMPTY = new Sequent(Collections.emptyList(), Collections.emptyList());

    private final ProofFormula antecedent[];
    private final ProofFormula succedent[];

    public Sequent(Collection<ProofFormula> ante, Collection<ProofFormula> succ) {
        this.antecedent = Util.toArray(ante, ProofFormula.class);
        this.succedent = Util.toArray(succ, ProofFormula.class);
    }

    public List<ProofFormula> getAntecedent() {
        return Util.readOnlyArrayList(antecedent);
    }

    public List<ProofFormula> getSuccedent() {
        return Util.readOnlyArrayList(succedent);
    }

    public static Sequent singleAntecedent(ProofFormula formula) {
        return new Sequent(Collections.singleton(formula), Collections.emptyList());
    }

    public static Sequent singleSuccedent(ProofFormula formula) {
        return new Sequent(Collections.emptyList(), Collections.singleton(formula));
    }

    public boolean isEmpty() {
        return antecedent.length + succedent.length == 0;
    }

    @Override
    public String toString() {
        return (Util.commatize(antecedent) + " |- " +
                Util.commatize(succedent)).trim();
    }

    public Sequent union(Sequent other) {
        ArrayList<ProofFormula> ante = new ArrayList<>();
        ante.addAll(getAntecedent());
        ante.addAll(other.getAntecedent());
        Util.removeDuplicates(ante);

        ArrayList<ProofFormula> succ = new ArrayList<>();
        succ.addAll(getSuccedent());
        succ.addAll(other.getSuccedent());
        Util.removeDuplicates(succ);

        return new Sequent(ante, succ);
    }
}
