package edu.kit.iti.algover.proof;


import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.SymbexPath;

import java.util.LinkedList;
import java.util.List;

/**
 * Created by sarah on 8/22/16.
 */
public class PVC {
    private String name;

    public String getName() {
        return name;
    }

    public int getPvcID() {
        return pvcID;
    }

    public ScriptTree getLocalScript() {
        return localScript;
    }

    public List<TopFormula> getAssumptionsWithInfo() {
        return assumptionsWithInfo;
    }

    public List<TopFormula> getGoalWithInfo() {
        return goalWithInfo;
    }

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public DafnyDecl getParent() {
        return parent;
    }

    /**
     * ID of proof verification condition, has to be unique
     */
    private int pvcID;

    /**
     * local script of pvc, is identified by id
     */
    private ScriptTree localScript;

    /**
     * List of terms for the "toplevel" formula representing assumptions
     */
    private List<TopFormula> assumptionsWithInfo;

    /**
     * List of terms for the "toplevel" formula representing goals
     */

    private List<TopFormula> goalWithInfo;
    /**
     * Path through programm
     */
    private SymbexPath pathThroughProgram;

    /**
     *DafnDecl this PVC belongs to
     */
    private DafnyDecl parent;

    /**
     * The variable map containing all assignments, for display of substitutions in terms
     */
    //private VariableMap variableMap;

    /**
     * The object representing a Proofverification condition. This PVC is a logical representation of the proof state after symbolic execution
     * @param builder
     */

    public PVC(PVCBuilder builder){
        this.pvcID = builder.getPvcID();
        this.name = builder.getPvcName();
        this.pathThroughProgram = builder.getPathThroughProgram();
        this.parent = builder.getParent();
        this.goalWithInfo = builder.getGoalWithInfo();
        this.assumptionsWithInfo = builder.getAssumptionsWithInfo();
      //  this.variableMap = pathThroughProgram.getMap();
       // this.localScript = builder.getLocalScript();

    }

    public String toString(){
        String ret = "ProofVerificationCondition #"+this.pvcID+"\n"+
                this.name+"\n";
            for (TopFormula tf : assumptionsWithInfo) {
                if (tf != null) {
                    ret += tf.toString() + "\n";
                }

            }
        ret+= "Goal: ";
        for(TopFormula tf: goalWithInfo){
            if(tf != null) {
                ret += tf.toString() + "\n";
            }
        }
        return ret;
    }
}
