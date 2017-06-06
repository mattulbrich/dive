/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;


import java.util.List;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCBuilder;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.SinglePVC;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Visitor for DafbnyDecl, that performs symbex on dafnydecl and returns PVCCollection
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

    // REVIEW: Remove parameter
    public DafnyDeclPVCCollector(ProjectFacade facade){
        this.facade = facade;
    }

    public PVCCollection visitClass(DafnyClass cl, PVCCollection parent) {
        PVCGroup clGroup = new PVCGroup(cl);

        for(DafnyFunction f :cl.getFunctions()) {
            clGroup.addChild(visitFunction(f, clGroup));
        }

        for(DafnyMethod m :cl.getMethods()) {
            clGroup.addChild(visitMethod(m, clGroup));
        }

        return clGroup;
    }

    public PVCCollection visitMethod(DafnyMethod m, PVCCollection parent) {
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

    public PVCCollection visitFunction(DafnyFunction f, PVCCollection parent) {
        PVCGroup mGroup = new PVCGroup(f);

        // TODO: NOT YET IMPLEMENTED

        return mGroup;
    }

    // no collection per file!
    public void visitFile(DafnyFile file, PVCCollection collection) {
        for (DafnyFunction f : file.getFunctions()) {
            visitFunction(f, collection);
        }

        for(DafnyMethod m : file.getMethods()) {
            visitMethod(m, collection);
        }
    }

}
