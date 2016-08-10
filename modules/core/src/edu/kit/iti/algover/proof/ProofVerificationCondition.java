package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Term;

import java.util.List;

/**
 * For each path and invariant part/ensures part one single pvc
 * This class represents a root PVC that will be referenced by the proof
 */
public class ProofVerificationCondition {
    private String pvcID;

    private List<Term> assumptions;
    private List<Term> pathconditions;
    private List<Term> goals;
    private int[] pathlines;

   private SymbexPath path;


public ProofVerificationCondition(String id, List<Term> assumptions, List<Term> pathconditions, List<Term> goal, int[] pathlines){
    this.pvcID = id;
    this.assumptions = assumptions;
    this.pathconditions = pathconditions;
    this.goals = goal;
    this.pathlines = pathlines;
}

    public String toString(){
        return "PVC "+pvcID.toString()+"\n"+assumptionsToString()+pathconditionsToString()+"\n==>\n"+goalsToString();

    }

    private String goalsToString() {
        String ret = "";
        for (Term goal: goals) {
            ret += goal.toString() + ",\n";
        }
        return ret;
    }


    private String assumptionsToString(){
        String ret = "";
        for (Term assumption: assumptions) {
            ret += assumption.toString() + ",\n";
        }
        return ret;
    }

    private String pathconditionsToString(){
        String ret = "";
        for (Term pathcondition: pathconditions) {
            ret += pathcondition.toString() + ",\n";
        }
        return ret;
    }

}
