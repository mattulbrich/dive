/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

/**
 * Interface for datastructure, that represents all PVCs of a project as a composite structure with pointers to the Project object.
 * Created by sarah on 10/19/16.
 */

public abstract class PVCCollection {

    private PVCCollection parent;

    public abstract DafnyDecl getDafnyDecl();

    public abstract PVCCollection getRoot();

    public abstract boolean isPVCLeaf();

    public abstract List<PVCCollection> getChildren();

    public PVCCollection getParent() {
        return parent;
    }

    protected void setParent(PVCCollection parent) {
        this.parent = parent;
    }

}
