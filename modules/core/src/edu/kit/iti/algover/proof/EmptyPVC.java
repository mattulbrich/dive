package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.Collections;
import java.util.List;

/**
 * Created by sarah on 10/23/16.
 */
public class EmptyPVC extends PVCCollection {
    DafnyDecl dd;
    public EmptyPVC(DafnyDecl dd){
        this.dd=dd;
    }
    @Override
    public List<PVCCollection> getPVCsForDafnyDecl(DafnyDecl d) {
        return Collections.emptyList();
    }

    @Override
    public DafnyDecl getDafnyDecl() {
        return this.dd;
    }

    @Override
    public void addPVC(PVC pvc) {

    }

    @Override
    public void addChild(PVCCollection col) {

    }

    @Override
    public String toString() {
        return "No PVC";
    }

    @Override
    public PVCCollection getRoot() {
        return null;
    }

    @Override
    public boolean isPVCLeaf() {
        return true;
    }
}
