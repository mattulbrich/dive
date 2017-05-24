/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.project.Project;

/**
 * Class holding all infos about the different pvcs and their references in the project
 * Created by sarah on 10/19/16.
 */

// REVIEW: Suggest to remove this class -> ProjectFacade does the trick.

@Deprecated
public class ProofManagement {

    // REVIEW: root does not seem to be set.
    private PVCGroup root;

    // REVIEW: Is ProjectFacade not a singleton?
    // private ProjectFacade facade;

    public PVCCollection getProofverificationconditions() {
        return root;
    }

    public PVCGroup getRoot() {
        return root;
    }

    public ProofManagement(Project p) {
        this.root = ProjectFacade.getInstance().generateAndCollectPVC(p);
    }

    // This code is not in ProjectFacade#generateAndCollectPVC
//    private static PVCCollection createPVCCollection(Project p){
//
//        PVCGroup root = new PVCGroup(null);
//
//        DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(p);
//
//        for (DafnyFile file : p.getDafnyFiles()) {
//            visitor.visitFile(file, root);
//        }
//
//        return root;
//
//    }

}
