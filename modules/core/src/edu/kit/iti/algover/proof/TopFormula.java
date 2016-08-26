package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.util.Pair;

import java.util.List;

/**
 * Represents formula, with references to origin
 * Created by sarah on 8/18/16.
 */
public class TopFormula{
    /**
     * ID of parent PVC
     */
    private int pvcID;
    /**
     * Position whether in assumption or goal
     */

    private boolean goalFormula;
    /**
     * Term that is represented (has to be toplevel term)
     */
    private Term t;

    /**
     * Term that represents all lets
     */
    private Term letTerm;
    /**
     * ID of ToplevelFormula for references
     */
    private int idInPVC;

    /**
     * Symbexpath the term belongs to
     */
    private SymbexPath path;

    /**
     * filename of file where term is in
     */
    private String filename;
    /**
     * Position in file (atm only line)
     */
    private int lineInFile;

    /**
     * Is set if we have a path condition
     */
    private PathConditionElement pce;

    /**
     * Is set if we have a goal formula
     */
    private AssertionElement ae;

    public TopFormula(Term t, Term letTerm, int id, SymbexPath path, int line, PathConditionElement pce, int pvcID){

        this.t = t;
        this.idInPVC = id;
        this.path = path;
        this.lineInFile = line;
        this.letTerm = letTerm;
        this.pce = pce;
        this.goalFormula = false;
        this.pvcID = pvcID;

    }

    public TopFormula(Term t, Term letTerm, int id, SymbexPath path, int line, AssertionElement ae, int pvcID ){

        this.t = t;
        this.idInPVC = id;
        this.path = path;
        this.lineInFile = line;
        this.letTerm = letTerm;
        this.ae = ae;
        this.goalFormula = true;
        this.pvcID = pvcID;

    }
//to get all substitutions the subterms have to be visited
    public String toString(){
/*        if(letTerm instanceof LetTerm){
            System.out.println(letTerm);
            LetTerm t = (LetTerm) letTerm;

            System.out.println("Let Term Subs: ");

            for(Pair<FunctionSymbol, Term> term : t.getSubstitutions()){
                System.out.println(term.fst.toString() + " is equal to "+ term.getSnd());
            }
        }*/
        String goalFormula = "";
        if(this.isGoalFormula()){
            goalFormula = "Goal";
        }else{
            goalFormula = "Pathcondition";
        }
        return "TopFormula #"+idInPVC+" "+goalFormula+": \n"+t.toString()+" refers to Line "+lineInFile;

    }
    public boolean isGoalFormula(){
        return this.goalFormula;
    }

    public boolean isAssumptionFormula(){
        return !this.goalFormula;
    }







}
