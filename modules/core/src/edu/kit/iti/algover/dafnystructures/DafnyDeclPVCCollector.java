/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;


import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.List;

/**
 * Visitor for DafnyDecl, that performs symbex on dafnydecl and returns PVCCollection
 * Created by sarah on 10/20/16.
 * refactored by mattias
 */
public class DafnyDeclPVCCollector {

    // REVIEW: Is ProjectFacade not a singleton? --> remove
    private final ProjectFacade facade;

    /**
     * The counter to create uniquely numbered PVCs.
     */
    private int counter;

    // REVIEW: Remove parameter -- it is a singleton after all.
    public DafnyDeclPVCCollector(ProjectFacade facade){
        this.facade = facade;
    }

    public PVCCollection visitClass(DafnyClass cl) {
        PVCGroup clGroup = new PVCGroup(cl);

        for(DafnyFunction f :cl.getFunctions()) {
            clGroup.addChild(visitFunction(f));
        }

        for(DafnyMethod m :cl.getMethods()) {
            clGroup.addChild(visitMethod(m));
        }

        return clGroup;
    }

    public PVCCollection visitMethod(DafnyMethod m) {
        PVCGroup mGroup = new PVCGroup(m);

        Symbex symbex = new Symbex();
        List<SymbexPath> paths = symbex.symbolicExecution(m.getRepresentation());
        for (SymbexPath path : paths) {
            List<SymbexPath> subpaths = path.split();
            for (SymbexPath subpath : subpaths) {
                PVCBuilder builder = new PVCBuilder();
                builder
                    .setPvcID(counter)
                    .setPathThroughProgram(subpath)
                    .setDeclaration(m);
                counter++;

                PVC pvc;
                try {
                    pvc = builder.build();
                    SinglePVC sPVC = new SinglePVC(pvc);
                    mGroup.addChild(sPVC);
                } catch (TermBuildException e) {
                    // FIXME. ... need a concept ofr exception handling here
                    e.printStackTrace();
                }
            }
        }

        return mGroup;
    }

    public PVCCollection visitFunction(DafnyFunction f) {
        PVCGroup mGroup = new PVCGroup(f);

        // TODO: NOT YET IMPLEMENTED

        return mGroup;
    }

    // no collection per file!
    public void visitFile(DafnyFile file, PVCGroup collection) {
        for (DafnyFunction f : file.getFunctions()) {
            collection.addChild(visitFunction(f));
        }

        for(DafnyMethod m : file.getMethods()) {
            collection.addChild(visitMethod(m));
        }

        for(DafnyClass c : file.getClasses()) {
            collection.addChild(visitClass(c));
        }
    }


}
