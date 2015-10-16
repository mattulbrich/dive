package edu.kit.iti.algover.Proof;

import edu.kit.iti.algover.term.Term;

import java.util.LinkedList;

/**
 * Created by sarah on 10/7/15.
 */
public class ProofFormula {

    private int id;
    private Term formula;
    private String label;
    private LinkedList<FormulaInheritance> comesFrom;

    public ProofFormula(int id, Term formula, String label) {
        this.id = id;
        this.formula = formula;
        this.label = label;
    }
}
