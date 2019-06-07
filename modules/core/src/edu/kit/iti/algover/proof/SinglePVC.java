/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.Collections;
import java.util.List;

/**
 * Represents a single PVC belonging to a PVCGroup
 * Created by sarah on 10/19/16.
 */
public class SinglePVC extends PVCCollection {

    private final PVC pvc;

    public SinglePVC(PVC pvc) {
        this.pvc = pvc;
    }

    public PVC getPVC() {
        return pvc;
    }

    @Override
    public DafnyDecl getDafnyDecl() {
        return getParent().getDafnyDecl();
    }

    @Override
    public String toString() {
        return pvc.toString();
    }

    @Override
    public boolean isPVCLeaf() {
        return true;
    }

    @Override
    public List<PVCCollection> getChildren() {
        return Collections.emptyList();
    }

    @Override
    protected void addTo(List<PVC> result) {
        result.add(pvc);
    }

}
