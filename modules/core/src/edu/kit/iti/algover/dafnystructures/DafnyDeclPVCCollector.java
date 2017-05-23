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
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.SinglePVC;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;

/**
 * Visitor for DafbnyDecl, that performs symbex on dafnydecl and returns PVCCollection
 * Created by sarah on 10/20/16.
 * refactored by mattias
 */
public class DafnyDeclPVCCollector {

    private Project facade;

    public DafnyDeclPVCCollector(Project facade){
        this.facade = facade;
    }

    public PVCCollection visitClass(DafnyClass cl, PVCCollection parent) {
        PVCGroup clGroup = new PVCGroup(cl);

        for(DafnyFunction f :cl.getFunctions()){
            clGroup.addChild(visitFunction(f, clGroup));
        }

        for(DafnyMethod m :cl.getMethods()){
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
                PVC pvc = new PVC(subpath);
                SinglePVC sPVC = new SinglePVC(pvc);
                mGroup.addChild(sPVC);
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
