/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.util.ObservableValue;

import java.io.IOException;
import java.util.Collections;
import java.util.Map;

/**
 * The base class for the implementations of Project Manager.
 *
 * It contains the common data structures and methods.
 *
 * See {@link ProjectManager} for Javadoc comments of the methods.
 *
 * @author mulbrich
 *
 * REVIEW: moved from ObservableValue back to simple value since observability
 * has not been used yet at all.
 *
 */
public abstract class AbstractProjectManager implements ProjectManager {

    /**
     * The project managed in this object.
     *
     * The project may change when {@link #reload()} is called.
     */
    private Project project;

    /**
     * Map from PVC identifiers to corr. proofs.
     *
     * Invariant: There exists a proof for every identifier within the project.
     */
    protected Map<String, Proof> proofs = Collections.emptyMap();


    @Override
    public Proof getProofForPVC(String pvcIdentifier) {
        return getAllProofs().get(pvcIdentifier);
    }

    @Override
    public Map<String, Proof> getAllProofs() {
        return Collections.unmodifiableMap(proofs);
    }

    @Override
    public Map<String, PVC> getPVCByNameMap() {
        return getProject().getPVCByNameMap();
    }

    @Override
    public Project getProject() {
        // return project.getValue();
        return project;
    }

    @Override
    public PVCGroup getAllPVCs() {
        return getProject().getAllPVCs();
    }

    @Override
    public void saveProject() throws IOException {
        for (Map.Entry<String, Proof> pvcProofEntry : proofs.entrySet()) {
            String pvcName = pvcProofEntry.getKey();
            Proof proof = pvcProofEntry.getValue();
            saveProofScriptForPVC(pvcName, proof);
        }
    }

    /**
     * Update the project of the observable value.
     *
     * @param project the new project to use
     */
    protected void setProject(Project project) {
        // this.project.setValue(project);
        this.project = project;
    }
}
