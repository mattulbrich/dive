/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.List;

/**
 * Interface for datastructure,
 * that represents all PVCs of a project as a composite structure with pointers to the Project object.
 * @author S. Grebing
 */

public abstract class PVCCollection {

    /**
     * The parent Collection (if the PVCCollection is part of a class or method for example)
     */
    private PVCCollection parent;

    /**
     * Get teh corresponsing DafnyDecl for this PVCCollection
     *
     * @return
     */
    public abstract DafnyDecl getDafnyDecl();

    /**
     * Return the root, inorder to traverse children
     * @return
     */
    public abstract PVCCollection getRoot();

    /**
     * If this PVCCollection is a SinglePVC it is a leaf.
     * @return
     */
    public abstract boolean isPVCLeaf();


    public abstract List<PVCCollection> getChildren();

    public PVCCollection getParent() {
        return parent;
    }

    protected void setParent(PVCCollection parent) {
        this.parent = parent;
    }

    public abstract PVCCollection getChild(int i);

}
