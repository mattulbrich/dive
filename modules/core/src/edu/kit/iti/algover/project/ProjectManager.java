/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.util.FormatException;

import java.io.IOException;
import java.util.Map;

public interface ProjectManager {
    void reload() throws DafnyException, DafnyParserException, IOException, FormatException;

    String loadScriptForPVC(String pvc) throws IOException;

    Proof getProofForPVC(String pvcIdentifier);

    Map<String, Proof> getAllProofs();

    void saveProject() throws IOException;

    void saveProofScriptForPVC(String pvcIdentifier, Proof proof) throws IOException;

    Map<String, PVC> getPVCByNameMap();

    Project getProject();

    PVCGroup getPVCGroup();

    String getName();
}
