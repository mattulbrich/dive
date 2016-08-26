package edu.kit.iti.algover.proof;


import edu.kit.iti.algover.project.DafnyDecl;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Term;

import java.util.List;

/**
 * Created by sarah on 8/22/16.
 */
public class PVC {
    private String name;
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


    public PVC(PVCBuilder builder){
        this.pvcID = builder.getPvcID();
        this.name = builder.getPvcName();
        this.pathThroughProgram = builder.getPathThroughProgram();
        this.parent = builder.getParent();
       // this.goalWithInfo = builder.getGoalWithInfo();
        this.assumptionsWithInfo = builder.getAssumptionsWithInfo();
       // this.localScript = builder.getLocalScript();

    }

    public String toString(){
        String ret = "ProofVerificationCondition #"+this.pvcID+"\n"+
                this.name+"\n";
        for(TopFormula tf: assumptionsWithInfo){
            ret+= tf.toString()+"\n";
        }
        return ret;
    }
}
