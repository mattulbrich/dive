package edu.kit.iti.algover.proof;

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
    public Term getTerm(){ return this.formula;}
    public void addLabel(String s){
        label += "," + s;
    }
    public String toString(){
        if (label !=""){

            return id+"["+label+"]: "+formula.toString();
        }else{
            return id+ ": "+formula.toString();
        }
    }
}