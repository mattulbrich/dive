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


public class ProofFormula {

    /**
     * The ID of this formula. Must be unique in the context of the PVC.
     */
    private final int id;

    /**
     * The actual term which is captured in this object.
     */
    private final Term formula;

    /**
     * String for path label if nececssary
     */
    private final String label;


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

        if (label != null) {
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
