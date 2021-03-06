/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import nonnull.Nullable;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents grouping of PVCs. E.g. a class groups methods, that group SinglePVCs
 *
 */
public class PVCGroup extends PVCCollection {

    // REVIEW: dd is not a good field name
    private final @Nullable DafnyDecl dd;
    private final List<PVCCollection> children;

    public PVCGroup(@Nullable DafnyDecl dd){
        this.dd = dd;
        this.children = new ArrayList<>();
    }

 //   @Override
 //   public PVC getPVC() {
 //       return null;
 //   }

    @Override
    public DafnyDecl getDafnyDecl(){
        return this.dd;
    }

    public void addChild(PVCCollection col){
        children.add(col);
        col.setParent(this);
    }

    @Override
    public String toString() {
        return "PVCGroup[" + dd + "]";
    }

    @Override
    public boolean isPVCLeaf() {
        return false;
    }

    @Override
    public PVC getPVC() {
        throw new UnsupportedOperationException("This is not a leaf");
    }

    @Override
    public List<PVCCollection> getChildren() {
        return children;
    }

    @Override
    protected void addTo(List<PVC> result) {
        // TODO Auto-generated method stub
        getChildren().forEach(x -> x.addTo(result));
    }
}
