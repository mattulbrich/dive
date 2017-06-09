/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.term.Term;

/**
 * Created by sarah on 10/7/15.
 */
// REVIEW: Same as TopFormula?

public class ProofFormula {

    /**
     * The ID of this formula. Must be unique in the context of the PVC.
     */
    private final int id;

    /**
     * The actual term which is captured in this object.
     */
    private final Term formula;

    // REVIEW: dont know its purpose
    private final String label;

//    // REVIEW: is this obsolete now?
//    private LinkedList<FormulaInheritance> comesFrom;

    public ProofFormula(int id, Term formula, String label) {
        this.id = id;
        this.formula = formula;
        this.label = label;
    }

    public ProofFormula(int id, Term formula) {
        this.id = id;
        this.formula = formula;
        this.label = null;
    }


    public Term getTerm() {
        return this.formula;
    }

    @Override
    public String toString(){
        // REVIEW: !!!!! String comparison in Java does not work like this. Strings are objects not primitive values.
        if (label != "") {
            return id + "[" + label + "]: " + formula.toString();
        } else {
            return id + ": " + formula.toString();
        }
    }

    public int getID() {
        return id;
    }

    public String getLabel() {
        return label;
    }
}
