/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;


import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;

/**
 * Created by sarah on 8/22/16.
 */
public class PVC {
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
    /**
     * local script of pvc
     */
    private ScriptTree localScript;

    /**
     * Instantiates a new PVC. The informations are taken from a builder object.
     *
     * @param builder the builder to take relevant info from, not <code>null</code>.
     * @see PVCBuilder#build()
     */
    public PVC(PVCBuilder builder) {
        this.pvcID = builder.getPvcID();
        this.pathThroughProgram = builder.getPathThroughProgram();
        this.declaration = builder.getDeclaration();
        this.sequent = builder.getSequent();
    }

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

    /**
     * The variable map containing all assignments, for display of substitutions in terms
     */
    // private VariableMap variableMap;

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    @Override
    public String toString(){
        String ret = "PVC #"+this.pvcID+": " +
                this.getName();
        return ret;
    }

    public Sequent getSequent() {
        return sequent;
    }

}
