package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import java.util.List;

/**
 * Interface for datastructure, that represents all PVCs of a project as a composite structure with pointers to the Project object.
 * Created by sarah on 10/19/16.
 */
public abstract class PVCCollection {

    public abstract List<PVCCollection> getPVCsForDafnyDecl(DafnyDecl d);

    public abstract DafnyDecl getDafnyDecl();

    public abstract void addPVC(PVC pvc);

    public abstract void addChild(PVCCollection col);

    public abstract String toString();
}
