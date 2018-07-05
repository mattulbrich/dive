/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.term.Term;

/**
 * This class represents a single formula in the sequent
 */

// REVIEW: Please add equals/hashcode methods. Influence of label and id on equality
public class ProofFormula {


    /**
     * The actual term which is captured in this object.
     */
    private final Term formula;

    /**
     * String for path label if nececssary
     */
    private final String label;


    public ProofFormula(Term formula, String label) {
        this.formula = formula;
        this.label = label;
    }

    public ProofFormula(Term formula) {
        this.formula = formula;
        this.label = null;
    }


    public Term getTerm() {
        return this.formula;
    }

    @Override
    public String toString(){

        if (label != null) {
            return "[" + label + "]: " + formula.toString();
        } else {
            return formula.toString();
        }
    }

    /*public int getID() {
        return id;
    }*/

    public String getLabel() {
        return label;
    }
}
