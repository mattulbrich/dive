/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;


import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.SymbexPath;

/**
 * Created by sarah on 8/22/16.
 */
public class PVC {
    /**
     * local script of pvc, is identified by id
     */
    // REVIEW: did not understand "is identified by"
    private ScriptTree localScript;

    /**
     * ID of proof verification condition, has to be unique
     */
    // TODO not clear at the moment whether needed or where it comes from.
    private int pvcID;

    /**
     * List of terms for the "toplevel" formula representing assumptions.
     * This is created lazily on demand.
     */
    private List<TopFormula> assumptionsWithInfo;

    /**
     * List of terms for the "toplevel" formula representing goals
     */
    // REVIEW: Is this really a list of goals?
    private List<TopFormula> goalWithInfo;

    /**
     * Path through program. Not <code>null</code>
     */
    private SymbexPath pathThroughProgram;

    /**
     * DafnDecl this PVC belongs to. not <code>null</code>
     */
    private DafnyDecl declaration;

    public String getName() {
        return pathThroughProgram.getPathIdentifier();
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

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    /**
     * The variable map containing all assignments, for display of substitutions in terms
     */
    // private VariableMap variableMap;

    /**
     * Instantiates a new PVC. The informations are taken from a builder object.
     *
     * @param builder
     *            the builder to take relevant info from, not <code>null</code>.
     * @see PVCBuilder#build()
     */
    public PVC(PVCBuilder builder){
        this.pvcID = builder.getPvcID();
        this.pathThroughProgram = builder.getPathThroughProgram();
        this.declaration = builder.getDeclaration();
        this.goalWithInfo = builder.getGoalWithInfo();
        this.assumptionsWithInfo = builder.getAssumptionsWithInfo();
    }

    public String toString(){
        String ret = "ProofVerificationCondition #"+this.pvcID+"\n"+
                this.getName()+"\n";
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
