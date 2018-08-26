/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.project;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.util.ObservableValue;

import java.util.Collections;
import java.util.Map;

public abstract class AbstractProjectManager implements ProjectManager {

    /**
     * The project managed in this object.
     *
     * The project may change when {@link #reload()} is called.
     */
    protected final ObservableValue<Project> project =
            new ObservableValue<>("ProjectManager.project", Project.class);

    /**
     * Map from PVC identifiers to corr. proofs.
     *
     * Invariant: There exists a proof for every identifier within the project.
     */
    protected Map<String, Proof> proofs;

    /**
     * Return Proof object for a PVC if it exists, null otherwise
     *
     * @param pvcIdentifier
     * @return
     */
    @Override
    public Proof getProofForPVC(String pvcIdentifier) {
        return getAllProofs().get(pvcIdentifier);
    }

    @Override
    public Map<String, Proof> getAllProofs() {
        return Collections.unmodifiableMap(proofs);
    }

    /**
     * Get the plain PVCs as Map from pvcName -> PVC object
     *
     * @return
     */
    @Override
    public Map<String, PVC> getPVCByNameMap() {
        return this.project.getValue().getPVCByNameMap();
    }

    @Override
    public Project getProject() {
        return project.getValue();
    }

    /**
     * Return  all PVCs for the loaded project
     *
     * @return PVCGroup that is the root for all PVCs of the loaded project
     */
    @Override
    public PVCGroup getPVCGroup() {
        return this.getProject().getAllPVCs();
    }
}
