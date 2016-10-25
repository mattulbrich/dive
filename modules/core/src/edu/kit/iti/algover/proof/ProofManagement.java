package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.project.Project;

import java.util.HashMap;
import java.util.List;
import java.util.TreeMap;

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
        List<DafnyMethod> freeMethods = p.getMethods();
        List<DafnyFunction> freeFunctions = p.getFunctions();
        List<DafnyClass> classes = p.getClasses();

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
