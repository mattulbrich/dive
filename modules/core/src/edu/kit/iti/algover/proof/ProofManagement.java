/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDeclPVCCollector;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
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
    public static PVCCollection createPVCCollection(Project p){

        PVCGroup root = new PVCGroup(null);

        DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(p);

        for (DafnyFile file : p.getDafnyFiles()) {
            visitor.visitFile(file, root);
        }

        return root;

    }

}
