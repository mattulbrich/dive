/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.PVCSequenter;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.TreeUtil;

import java.util.ArrayList;
import java.util.Collection;

/**
 * A PVC corresponds to a symbexpath. So it consists of assignments on the path through the program of
 * pathconditions and of a goal to prove. In addition it is uniquely identified by its ID. This ID has to be given from a central instance
 * New attempt to implement a PVC Builder.
 *
 * REVIEW: Is this a builder for method PVCs? I assume so. If so, rename it accordngly.
 *
 * This class is not ready for multi-threading.
 *
 * Created by sarah on 8/18/16.
 */
public class PVCBuilder {
    /**
     * Counter for IDs for TopFormulas
     */
    private int formulaCounter = 0;

    /**
     * ID of proof verification condition, has to be unique
     */
    // REVIEW: What are the benefits of an integer ID?
    /* I think it would rather be very important that the PO/PVCs have
     * a unique srting id. In KeY, they had numbers at one point. Adding
     * a single new method threw every finished proof overboard.
     *
     * Are there benefits in integer Ids?
     */
    private int pvcID;

    /**
     * local script of pvc, is identified by id
     */
    //private ScriptTree localScript;

    /**
     * Path through program which represents state of this pvc
     */
    private SymbexPath pathThroughProgram;

    private PVCSequenter sequenter;

    /**
     * DafnyDecl to which this PVC belongs
     */
    private DafnyDecl declaration;

    public PVCBuilder() { }

    public int getPvcID() {
        return pvcID;
    }

    public PVCBuilder setPvcID(int pvcID) {
        this.pvcID = pvcID;
        return this;
    }

   /* public ScriptTree getLocalScript() {
        return localScript;
    }*/

   /* public PVCBuilder setLocalScript(ScriptTree localScript) {
        this.localScript = localScript;
        return this;
    }*/

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public PVCBuilder setPathThroughProgram(SymbexPath pathThroughProgram) {
        this.pathThroughProgram = pathThroughProgram;
        return this;
    }

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    public PVCBuilder setDeclaration(DafnyDecl decl) {
        this.declaration = decl;
        return this;
    }

    public PVC build() throws TermBuildException {
        formulaCounter = 0;
        return new PVC(this);
    }

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        // FIXME: This builder is probably meant only for methods. store method instead of declaration
        DafnyMethod method = (DafnyMethod) declaration;

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method.getRepresentation())) {
            String name = decl.getChild(0).toString();
            Sort sort = TreeUtil.toSort(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    public Sequent getSequent() {
        PVCSequenter sequenter = this.sequenter;
        if(sequenter == null) {
            assert !PVCSequenter.INSTANCES.isEmpty() :
                "there is no PCVSequenter";
            sequenter = PVCSequenter.INSTANCES.get(0);
        }

        try {
            return sequenter.translate(pathThroughProgram, makeSymbolTable());
        } catch (DafnyException e) {
            // FIXME TODO Auto-generated catch block
            throw new Error(e);
        }
    }

    public PVCSequenter getSequenter() {
        return sequenter;
    }

    public void setSequenter(PVCSequenter sequenter) {
        this.sequenter = sequenter;
    }

}
