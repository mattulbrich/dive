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

    private PVCCollection proofverificationconditions;

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

        PVCGroup root = new PVCGroup(null);
        List<DafnyMethod> freeMethods = p.getMethods();
        List<DafnyFunction> freeFunctions = p.getFunctions();
        List<DafnyClass> classes = p.getClasses();

        for(DafnyMethod fm: freeMethods){
            DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(facade);
            /*PVCGroup fmGroup = new PVCGroup(fm);
            for(PVC pvc: facade.generateAndCollectPVC(fm)){
                SinglePVC singlePVc = new SinglePVC(fmGroup);
                singlePVc.addPVC(pvc);
                fmGroup.addChild(singlePVc);
            }*/
            root.addChild(visitor.visit(fm, null));
        }
        for(DafnyFunction fm: freeFunctions){
            DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(facade);
          /*  PVCGroup fmGroup = new PVCGroup(fm);
            for(PVC pvc: facade.generateAndCollectPVC(fm)){
                SinglePVC singlePVc = new SinglePVC(fmGroup);
                singlePVc.addPVC(pvc);
                fmGroup.addChild(singlePVc);
            }*/
            root.addChild(visitor.visit(fm, null));
        }

        for(DafnyClass cl : classes){
            PVCGroup classGroup = new PVCGroup(cl);
            DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(facade);
            PVCCollection temp = visitor.visit(cl, null);

            //eigentlich rekursiver Aufruf
            root.addChild(temp);
        }
        return root;

    }

    public PVCCollection createPVCCollection(DafnyDecl dd){
        return null;
    }
}
