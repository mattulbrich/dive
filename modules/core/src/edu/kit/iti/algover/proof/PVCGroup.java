/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.ArrayList;

import java.util.List;

/**
 * Represents grouping of PVCs. E.g. a class groups methods, that group SinglePVCs
 * Created by sarah on 10/19/16.
 */
public class PVCGroup extends PVCCollection {

    private DafnyDecl dd;
    private List<PVCCollection> children;

    public PVCGroup(DafnyDecl dd){
        this.dd = dd;
        this.children = new ArrayList<>();
    }

    public PVCCollection getChild(int i){
        return children.get(i);
    }

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
    public PVCCollection getRoot() {
        if (getParent() == null) {
            return this;
        } else {
            return getParent().getRoot();
        }
    }

    @Override
    public boolean isPVCLeaf() {
        return false;
    }

    public List<PVCCollection> getChildren() {
        return children;
    }
}
