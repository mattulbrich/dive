/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.cli;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.DafnyProjectManager;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.FormatException;
import nonnull.NonNull;
import nonnull.Nullable;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

/**
 * A class which allows accessing the AlgoVer-System on a rather high level,
 * only specifying the directory to apply it on.
 *
 * @author Mattias Ulbrich
 */
public class AlgoVerService {

    /**
     * The default file name used for the configuration file.
     */
    public static final String DEFAULT_CONFIG_FILENAME = "config.xml";

    /**
     * The path of the project to analyse. It can be either a directory
     * or a .dfy file.
     */
    private final @NonNull File path;

    /**
     * The actually used configuration file name, defaults to
     * {@link #DEFAULT_CONFIG_FILENAME}.
     */
    private String configName = DEFAULT_CONFIG_FILENAME;

    /**
     * A filter to focus the analysis to the PVCs which are interesting.
     * Defaults to a predicate which does not filter at all.
     */
    private Predicate<PVC> pvcFilter = x -> true;

    /**
     * Verbosity flag.
     * If set to 1: Show progress on stderr
     * If set to 2: Print more info to stderr.
     * etc.
     */
    private int verbosityLevel = 0;

    /**
     * Intermediate result. The manager is stored after parsing.
     */
    private @Nullable ProjectManager projectManager = null;

    /**
     * Instantiate an AlgoVer run instance.
     *
     * @param path the path to the path or .dfy file
     *             containing config and code.
     */
    public AlgoVerService(@NonNull File path) {
        this.path = path;
    }

    /**
     * After setting the parameters, actually run the verification.
     *
     * @return the list of proofs created during the course of the verification.
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public @NonNull List<Proof> runVerification()
            throws DafnyParserException, IOException, DafnyException, FormatException {
        ProjectManager pm = getProjectManager();
        pm.reload();
        List<PVC> allPVCs = pm.getAllPVCs().getContents();
        List<Proof> allProofs = new ArrayList<>();
        for (PVC pvc : allPVCs) {
            if(pvcFilter.test(pvc)) {
                allProofs.add(processPVC(pm, pvc));
            }
        }

        return allProofs;
    }

    /*
     * Process one PVC at a time.
     */
    private Proof processPVC(ProjectManager pm, PVC pvc) throws IOException {
        String id = pvc.getIdentifier();
        Proof proof = pm.getProofForPVC(id);

        if (verbosityLevel > 0) {
            System.err.println("Working on " + id);
        }

        try {
            String script = pm.loadScriptForPVC(id);
            proof.setScriptText(script);
        } catch(FileNotFoundException ex) {
            if (verbosityLevel > 1) {
                System.err.println(" ... No script. Using default script.");
            }
        }

        if(verbosityLevel > 1) {
            PrettyPrint pp = new PrettyPrint();
            Sequent seq = pvc.getSequent();
            seq.getAntecedent().forEach(f -> System.err.println(pp.print(f.getTerm())));
            System.err.println("|-");
            seq.getSuccedent().forEach(f -> System.err.println(pp.print(f.getTerm())));
        }

        proof.interpretScript();
        ProofStatus status = proof.getProofStatus();

        if (verbosityLevel > 0) {
            System.err.println(" ... " + status);

            if(verbosityLevel > 1) {
                System.err.println(proof.proofToString());

                if (proof.getFailException() != null) {
                    proof.getFailException().printStackTrace();
                }
            }
        }

        return proof;
    }

    // Getters and setters ...

    public @NonNull File getPath() {
        return path;
    }

    public @NonNull String getConfigName() {
        return this.configName;
    }

    public void setConfigName(@NonNull String configName) {
        this.configName = configName;
    }

    public @NonNull Predicate<PVC> getPVCFilter() {
        return this.pvcFilter;
    }

    public void setPVCFilter(@NonNull Predicate<PVC> pvcFilter) {
        this.pvcFilter = pvcFilter;
    }

    public int getVerbosityLevel() {
        return verbosityLevel;
    }

    public void setVerbosityLevel(int verbosityLevel) {
        this.verbosityLevel = verbosityLevel;
    }

    /**
     * Create or retrieve the projectmanager for this service.
     *
     * This is good to separate parsing from actual verification.
     * @return the unique manager for this endevaour.
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public ProjectManager getProjectManager()
            throws DafnyParserException, IOException, DafnyException, FormatException {
        if (projectManager == null) {
            if (path.isDirectory()) {
                this.projectManager = new XMLProjectManager(path, configName);
            } else {
                this.projectManager = new DafnyProjectManager(path);
                this.projectManager.reload();
            }
        }
        return projectManager;
    }
}
