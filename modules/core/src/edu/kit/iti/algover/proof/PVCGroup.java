package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.ArrayList;

import java.util.List;

/**
 * Represents grouping of PVCs. E.g. a class groups methods, that group SinglePVCs
 * Created by sarah on 10/19/16.
 */
public class PVCGroup extends PVCCollection {
    boolean root = false;
    PVCCollection parent;
    DafnyDecl dd;

    List<PVCCollection> children;

    public PVCGroup(DafnyDecl dd, PVCCollection parent){
        if(dd == null){
            root = true;
            parent = null;
        }
        this.dd = dd;
        this.parent = parent;
        children = new ArrayList<>();
    }
    @Override
    public List<PVCCollection> getPVCsForDafnyDecl(DafnyDecl d) {
        List<PVCCollection> pvcs = new ArrayList<>();
        for(PVCCollection child: children){
            pvcs.addAll(getPVCsForDafnyDecl(d));
        }
        return pvcs;
    }

    public PVCCollection getChild(int i){
        return children.get(i);

    }

    public DafnyDecl getDafnyDecl(){
        return this.dd;
    }
    public void addChild(PVCCollection col){
        children.add(col);
    }

    @Override
    public String toString() {
        String s = "";
        if(root){
            s += "Root\n";
        }else{
            s+= "  Node for "+dd.getRepresentation().getType()+" "+dd.getName()+"\n";
        }
        /*for(PVCCollection col : children){
            if(col != null) {
                s += "  " + col.toString() + "\n";
            }
        }*/
        return s;
    }

    @Override
    public PVCCollection getRoot() {
        if(root){
            return this;
        }else {
            return parent.getRoot();
        }
    }

    @Override
    public boolean isPVCLeaf() {
        return false;
    }

    public void addPVC(PVC pvcImpl){
        if(pvcImpl.getParent().equals(dd)){
            SinglePVC pvc = new SinglePVC(this);
            pvc.addPVC(pvcImpl);
            children.add(pvc);
        }else{
            for(PVCCollection child:children){
                child.addPVC(pvcImpl);
            }
        }
    }

    public List<PVCCollection> getChildren() {
        return children;
    }
}
