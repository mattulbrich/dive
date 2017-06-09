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
import edu.kit.iti.algover.term.Sequent;

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
    private final int pvcID;

    /**
     * Path through program. Not <code>null</code>
     */
    private final SymbexPath pathThroughProgram;

    /**
     * DafnDecl this PVC belongs to. not <code>null</code>
     */
    private final DafnyDecl declaration;

    private final Sequent sequent;

    public String getName() {
        return pathThroughProgram.getPathIdentifier();
    }

    public int getPvcID() {
        return pvcID;
    }

    public ScriptTree getLocalScript() {
        return localScript;
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
        this.sequent = builder.getSequent();
    }

    // REVIEW toString oneliner
    @Override
    public String toString(){
        String ret = "PVC #"+this.pvcID+": " +
                this.getName();
//            for (TopFormula tf : assumptionsWithInfo) {
//                if (tf != null) {
//                    ret += tf.toString() + "\n";
//                }
//
//            }
//        ret+= "Goal: ";
//        for(TopFormula tf: goalWithInfo){
//            if(tf != null) {
//                ret += tf.toString() + "\n";
//            }
//        }
        return ret;
    }

    public Sequent getSequent() {
        return sequent;
    }

}
