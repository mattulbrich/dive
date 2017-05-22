/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.util.Collection;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDeclPVCCollector;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.project.Project;

/**
 * Class holding all infos about the different pvcs and their references in the project
 * Created by sarah on 10/19/16.
 */
public class ProofManagement {
    private Project p;

    public Project getProject() {
        return p;
    }

    public PVCCollection getProofverificationconditions() {
        return proofverificationconditions;
    }

    private PVCCollection proofverificationconditions;

    public PVCGroup getRoot() {
        return root;
    }

    private PVCGroup root;
    ProjectFacade facade;

    public ProofManagement(Project p, ProjectFacade facade){
        this.p = p;
        this.facade = facade;
        this.proofverificationconditions = createPVCCollection(this.p);

    }

    /**
     *
     * @param p
     * @return
     */
    public PVCCollection createPVCCollection(Project p){

        PVCGroup root = new PVCGroup(null, null);
        this.root = root;
        Collection<DafnyMethod> freeMethods = p.getMethods();
        Collection<DafnyFunction> freeFunctions = p.getFunctions();
        Collection<DafnyClass> classes = p.getClasses();

        for(DafnyMethod fm: freeMethods){
            DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(facade);
            root.addChild(visitor.visit(fm, root));
        }
        for(DafnyFunction fm: freeFunctions){
            DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(facade);
            root.addChild(visitor.visit(fm, root));
        }

        for(DafnyClass cl : classes){

            DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(facade);
            PVCCollection temp = visitor.visit(cl, root);
            root.addChild(temp);
        }
        return root;

    }

}
