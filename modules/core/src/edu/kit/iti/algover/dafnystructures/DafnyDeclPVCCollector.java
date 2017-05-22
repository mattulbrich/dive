/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;


import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.*;

import java.util.List;

/**
 * Visitor for DafbnyDecl, that performs symbex on dafnydecl and returns PVCCollection
 * Created by sarah on 10/20/16.
 */
public class DafnyDeclPVCCollector implements DafnyDeclVisitor<PVCCollection, PVCCollection > {

    private ProjectFacade facade;
    public DafnyDeclPVCCollector(ProjectFacade facade){
        this.facade = facade;
    }
    @Override
    public PVCCollection visitDefault(DafnyDecl d, PVCCollection parent) {
        return null;
    }

    @Override
    public PVCCollection visit(DafnyClass cl, PVCCollection arg) {
        System.out.println("Vistited class "+cl.getName());
        PVCGroup clGroup = new PVCGroup(cl, arg);


        for(DafnyFunction f :cl.getFunctions()){
            clGroup.addChild(f.accept(this, clGroup));
        }

        for(DafnyMethod f :cl.getMethods()){
            clGroup.addChild(f.accept(this, clGroup));
        }

        return clGroup;
    }

    @Override
    public PVCCollection visit(DafnyMethod m, PVCCollection arg) {
        System.out.println("Vistited method "+m.getName());
        PVCGroup mGroup = new PVCGroup(m, arg);
        List<PVC> pvcs = facade.generateAndCollectPVC(m);
        for(PVC pvc : pvcs){
            SinglePVC sPVC = new SinglePVC(mGroup);
            sPVC.addPVC(pvc);
            mGroup.addChild(sPVC);
        }
        return mGroup;
    }

    @Override
    public PVCCollection visit(DafnyFunction f, PVCCollection arg) {
        System.out.println("Vistited function "+f.getName());
        //return new SinglePVC(arg);
        return new EmptyPVC(f);
    }

    @Override
    public PVCCollection visit(DafnyField fi, PVCCollection arg) {
        System.out.println("Vistited field "+fi.getName());
        //return new SinglePVC(arg);
        return new EmptyPVC(fi);
    }
    @Override
    public PVCCollection visit(DafnyFile file, PVCCollection arg) {
        // TODO Auto-generated method stub
        return null;
    }
}
