package edu.kit.iti.algover.dafnystructures;


import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.SinglePVC;

import java.util.List;

/**
 * Visitor
 * Created by sarah on 10/20/16.
 */
public class DafnyDeclPVCCollector implements DafnyDeclVisitor<PVCCollection, Void > {

    private ProjectFacade facade;
    public DafnyDeclPVCCollector(ProjectFacade facade){
        this.facade = facade;
    }
    @Override
    public PVCCollection visitDefault(DafnyDecl d, Void arg) {
        return null;
    }

    @Override
    public PVCCollection visit(DafnyClass cl, Void arg) {
        System.out.println("Vistited class "+cl.getName());
        PVCGroup clGroup = new PVCGroup(cl);


        for(DafnyFunction f :cl.getFunctions()){
            clGroup.addChild(f.accept(this, null));
        }

        for(DafnyMethod f :cl.getMethods()){
            clGroup.addChild(f.accept(this, null));
        }

        return clGroup;
    }

    @Override
    public PVCCollection visit(DafnyMethod m, Void arg) {
        System.out.println("Vistited method "+m.getName());
        PVCGroup mGroup = new PVCGroup(m);
        List<PVC> pvcs = facade.generateAndCollectPVC(m);
        for(PVC pvc : pvcs){
            SinglePVC sPVC = new SinglePVC(mGroup);
            sPVC.addPVC(pvc);
            mGroup.addChild(sPVC);
        }
        return mGroup;
    }

    @Override
    public PVCCollection visit(DafnyFunction f, Void arg) {
        System.out.println("Vistited function "+f.getName());
        return null;
    }

    @Override
    public PVCCollection visit(DafnyField fi, Void arg) {
        System.out.println("Vistited field "+fi.getName());
        return null;
    }
}
