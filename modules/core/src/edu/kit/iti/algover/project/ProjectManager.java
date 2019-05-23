/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.util.FormatException;
import nonnull.NonNull;
import nonnull.Nullable;

import java.io.IOException;
import java.util.Map;

/**
 * The data structure to access Algover projects from UIs.
 *
 * A project manager is linked to a configuration entitiy (Dafny file or
 * config.xml-file) which defines the settings, relevant files and script
 * location.
 *
 * After construction, the project manager creates a project.
 *
 * Later by calling {@link #reload()}, a fresh project instance can be read from
 * disk (if files have been modified).
 *
 * There are several implementations for this interface.
 *
 * @author mulbrich
 */
public interface ProjectManager {

    /**
     * Reload the data from the underlying file resources.
     *
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot
     *                              be read
     * @throws FormatException      if the settings in the config file are
     *                              illegally formatted.
     */
    void reload() throws DafnyException, DafnyParserException, IOException, FormatException;

    /**
     * Retrieve an individual script for a PVC.
     *
     * The underlying datastrctures are not necessarily reloaded.
     *
     * @param pvc the PVC identifier to look up
     * @return the script stored for this identifier
     * @throws IOException if loading fails.
     */
    String loadScriptForPVC(@NonNull String pvc) throws IOException;

    /**
     * Return a proof object for a PVC if it exists, null otherwise
     *
     * @param pvcIdentifier the identifier of the PVC to find
     * @return null if there is no proof, yet. The corresponding proof otherwise.
     */
    @Nullable Proof getProofForPVC(@NonNull String pvcIdentifier);

    /**
     * Get a map from PVC identifiers to corresponding proof objects.
     *
     * The result map is indexed by PVC identifiers.
     *
     * @return an immutable view to the map of proofs.
     */
    @NonNull Map<String, Proof> getAllProofs();

    /**
     * Save all proof scripts to the underlying data structures.
     *
     * Unlike {@link #saveProofScriptForPVC(String, Proof)}, this method
     * always dumps proofs into file representation.
     */
    void saveProject() throws IOException;

    /**
     * Save the proof script for a PVC given by its interpreted proof.
     *
     * May be saved to file or to a memory datastructure.
     *
     * @param pvcIdentifier the name of the PVC
     * @param proof the proof from which to extract the script.
     * @throws IOException if saving fails.
     */
    void saveProofScriptForPVC(@NonNull String pvcIdentifier, @NonNull Proof proof) throws IOException;

    /**
     * Get a map from PVC identifiers to the actual PVCs.
     *
     * Equivalent to {@code getProject().getPVCByNameMap()}.
     *
     * @return an immutable view to the map.
     */
    Map<String, PVC> getPVCByNameMap();

    /**
     * Get the actual project currently stored in the manager.
     *
     * This may changed if reload is called!
     *
     * @return the relevant project object
     */
    @NonNull Project getProject();

    /**
     * Return  all PVCs for the loaded project.
     *
     * This is equivalent to calling {@code getProject().getAllPVCs()}.
     *
     * @return PVCGroup that is the root for all PVCs of the loaded project
     */
    @NonNull PVCGroup getAllPVCs();

    /**
     * Get a self-explanatory name of this project manager.
     *
     * It is usually derived from the file or directory which stores the
     * project description.
     *
     * @return a cleartext intuitive name for the manager
     */
    @NonNull String getName();

    /**
     * Get the current project contents as Configuration object
     * @return a configuration object
     */
    @NonNull Configuration getConfiguration();

    /**
     * Update project settings acc. to configuration
     * @param config
     */
    void updateProject(@NonNull Configuration config) throws IOException, DafnyParserException, FormatException, DafnyException;

    /**
     * Save the current project information
     * @throws IOException
     */
    void saveProjectConfiguration() throws IOException;
}
