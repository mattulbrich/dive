package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a single PVC belonging to a PVCGroup
 * Created by sarah on 10/19/16.
 */
public class SinglePVC extends PVCCollection {
    public PVC getPVC() {
        return pvc;
    }

    PVC pvc;
    DafnyDecl dd;
    PVCCollection parent;

    public SinglePVC(PVCCollection parent){
        this.parent = parent;
        this.dd = parent.getDafnyDecl();

    }
    @Override
    public List<PVCCollection> getPVCsForDafnyDecl(DafnyDecl d) {
        if(this.dd.equals(d)){
            List<PVCCollection> l = new ArrayList<>();
            l.add(this);
            return l;
        }
        return new ArrayList<>();
    }

    @Override
    public DafnyDecl getDafnyDecl() {
        return this.dd;
    }

    public void addPVC(PVC pvc){
        this.pvc = pvc;
    }

    @Override
    public void addChild(PVCCollection col){
        try {
            throw new Exception("Leafs do not have children");
        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    @Override
    public String toString() {
        return "    Leaf of "+dd.getName()+": "+pvc.getName();
    }

    @Override
    public PVCCollection getRoot() {
        return parent.getRoot();
    }

    @Override
    public boolean isPVCLeaf() {
        return true;
    }

    @Override
    public boolean isEmptyPVC() {
        return (this.pvc == null);
    }


}
