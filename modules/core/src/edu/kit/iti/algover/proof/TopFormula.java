package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.util.Pair;

import java.util.*;

/**
 * Represents formula, with references to origin. This Object should be immutable.
 * Created by sarah on 8/18/16.
 */
public class TopFormula{
    public int getParentPvcID() {
        return pvcID;
    }

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

    public Term getTerm() {
        return t;
    }

    public Term getLetTerm() {
        return letTerm;
    }

    public int getIdInPVC() {
        return idInPVC;
    }

    public int getLineInFile() {
        return lineInFile;
    }

    private List<Pair<String, DafnyTree>> affectingAssignments;
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

    private Set<String> varOccurence;
    private List<Pair<String, DafnyTree>> affectingUpdates;

    public TopFormula(Term t, Term letTerm, int id, SymbexPath path, int line, PathConditionElement pce, int pvcID){

        this.t = t;
        this.idInPVC = id;
        this.path = path;
        this.lineInFile = line;
        this.letTerm = letTerm;
        this.pce = pce;
        this.goalFormula = false;
        this.pvcID = pvcID;
        this.varOccurence = new HashSet<>(extractVariableNamesOfThisTerm());

        this.affectingAssignments = extractAffectingVarAssignments();


    }

    /**
     * TODO
     * Temp, needs to be written cleanly and put to right object
     * @return
     */
    private List<Pair<String, DafnyTree>> extractAffectingVarAssignments() {
        //get all Assignments on path
        VariableMap map = this.path.getMap();

        //initialize data structure for affecting assignments
        List<Pair<String, DafnyTree>> affectingAssignments = new LinkedList<>();
        Set<String> varNames = this.varOccurence;

        List<Pair<String, DafnyTree>> pairs = map.toList();
        Pair<String, DafnyTree> tempPair;
        DafnyTree tempTree;
        if(varNames != null){
            for(Pair<String, DafnyTree> pair : pairs){
                tempTree = null;
                tempPair = pair;
                for(String var : varNames){
                    if(tempPair.getFst().equals(var)){
                        affectingAssignments.add(tempPair);
                        tempTree = tempPair.getSnd();
                    }
                }
                if(tempTree != null){
                    varNames.addAll(getSubVars(tempTree));
                }
            }
        }

            /*ListIterator<Pair<String, DafnyTree>> iterator = pairs.listIterator();
            Pair<String, DafnyTree> tempPair;
            List<DafnyTree> tempTerms ;
            if (varNames != null) {

                while(iterator.hasNext()){
                    tempPair = iterator.next();
                    for (String var: varNames) {
                        if(tempPair.getFst().equals(var)){
                            tempTerms = new LinkedList<>();
                            affectingAssignments.add(tempPair);
                            //visit subterms and extract vars
                            tempTerms.add(tempPair.getSnd());
                           // varNames.addAll(getSubVars(tempPair.getSnd()));
                        }
                    }

                }
            }*/
        //}

        return affectingAssignments;

    }

    /**
     * Extract subterm variables from dafnytree term
     * @param t
     * @return List of variablenames
     */
    private List<String> getSubVars(DafnyTree t){
        LinkedList<String> subVars = new LinkedList<>();
        List<DafnyTree> childrenWith = t.getChildren();
        if(childrenWith != null) {
            for (DafnyTree child : childrenWith) {
                if (child.getType() == DafnyParser.ID) {
                    subVars.add(child.getText());
                }
            }
        }
        return subVars;
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

        extractAffectingVarAssignments();
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
        String affAssign = "";
        if (affectingAssignments != null) {
            affAssign += "Affecting Assignments:\n";
            for (Pair<String, DafnyTree> ass: affectingAssignments) {
               affAssign += ass.getFst()+" := "+ass.getSnd().toStringTree() +"\n";
            }
        }
      //  extractAffectingVarAssignments();
        return "TopFormula #"+idInPVC+" "+goalFormula+": \n"+t.toString()+" refers to Line "+lineInFile + "\n" + affAssign;

    }
    public boolean isGoalFormula(){
        return this.goalFormula;
    }

    public boolean isAssumptionFormula(){
        return !this.goalFormula;
    }

    private List<String> extractVariableNamesOfThisTerm(){
        VariableTermVisitor visitor = new VariableTermVisitor();
        List<String> list =  t.accept(visitor, null);
//        System.out.println(getTerm().toString());
//        for(String s : list){
//            System.out.println("Termcomponents: "+s+"\n");
//        }

        return list;
    }







}
