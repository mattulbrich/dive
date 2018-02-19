/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FileUtil;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ObservableValue;
import edu.kit.iti.algover.util.Util;
import nonnull.Nullable;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Supplier;

/**
 * REVIEW: This explanation does not really cover the purpose of this class.
 *
 * Class handling project and proof management
 *
 * @author Sarah Grebing
 * @author Mattias Ulbrich, refactored Jan 2018
 */
public final class ProjectManager {

    private static final String CONFIG_DEFAULT_NAME = ProjectBuilder.CONFIG_DEFAULT_FILENAME;

    /**
     * The project managed in this object.
     *
     * The project may change when {@link #reload()} is called.
     */
    private final ObservableValue<Project> project =
            new ObservableValue<>("ProjectManager.project", Project.class);

    /**
     * the name of the config.xml file within the directory.
     */
    private final String configFilename;

    /**
     * the directory in which the project resides.
     */
    private final File directory;

    /**
     * Map from PVC identifiers to corr. proofs.
     *
     * Invariant: There exists a proof for every identifier within the project.
     */
    private Map<String, Proof> proofs;

    // REVIEW Documentation?
    private Map<String, Supplier<String>> fileHooks = new HashMap<>();

    /**
     * Build a new project by parsing the config file and performing symbolic execution
     *
     * @param directory      the directory where the problem resides in
     * @param configFilename the filename of the configuration within this directory
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public ProjectManager(File directory, String configFilename) throws FormatException, DafnyParserException, IOException, DafnyException {
        this.directory = directory;
        this.configFilename = configFilename;
        reload();
    }

    /**
     * Build a new Project by parsing the config file and performing symbolic execution.
     *
     * <p>The configname is taken to be the default, i.e. {@link #CONFIG_DEFAULT_NAME}.
     *
     * @param directory      the directory where the problem resides in
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public ProjectManager(File directory) throws DafnyParserException, IOException, DafnyException, FormatException {
        this(directory, CONFIG_DEFAULT_NAME);
    }

    /**
     * Reload the project.
     *
     * <P>Reparse the source code and the config files and. Regenerate the proof objects throwing away existing
     * objects.
     *
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public void reload() throws DafnyException, DafnyParserException, IOException, FormatException {
        Project project = buildProject(directory, configFilename);
        generateAllProofObjects(project);
        this.project.setValue(project);
    }

    /**
     * Build a new Project by parsing the config file and performing symbolic execution
     *
     * @param path           the directory where the problem resides in
     * @param configFilename the filename of the configuration within this directory
     * @return a freshly created project read from the directory and configFilename
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    private static Project buildProject(File path, String configFilename)
            throws DafnyException, DafnyParserException, IOException, FormatException {
        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(path);
        pb.setConfigFilename(configFilename);
        try {
            pb.parseProjectConfigurationFile();
            pb.validateProjectConfiguration();
        } catch (JAXBException|SAXException e) {
            // subsume the XML exceptions under IOException.
            throw new IOException(e);
        }

        Project result = pb.build();

        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor refResolver = new ReferenceResolutionVisitor(result, exceptions);
        refResolver.visitProject();

        TypeResolution typeRes = new TypeResolution(exceptions);
        typeRes.visitProject(result);

        if(!exceptions.isEmpty()) {
            // TODO ->MU: Is it wise to only return the first exception?
            throw exceptions.get(0);
        }

        return result;
    }

    /**
     * Generate all proof all available PVCs.
     *
     * Load and parse the script text if present.
     */
    private void generateAllProofObjects(Project project) throws IOException {
        proofs = new HashMap<>();
        for (PVC pvc : project.getPVCByNameMap().values()) {
            Proof p = new Proof(project, pvc);
            String script;
            try {
                script = loadScriptForPVC(pvc.getIdentifier());
            } catch(FileNotFoundException ex) {
                script = project.getSettings().getString(ProjectSettings.DEFAULT_SCRIPT);
            }
            p.setScriptText(script);

            proofs.put(pvc.getIdentifier(), p);
        }
    }

    public String loadScriptForPVC(String pvc) throws IOException {
        // find file on disc
        File scriptFile = getScriptFileForPVC(pvc);

        if(!scriptFile.exists()) {
            throw new FileNotFoundException(scriptFile.getAbsolutePath());
        }

        return new String(Files.readAllBytes(scriptFile.toPath()));
    }

    public File getScriptFileForPVC(String pvcIdentifier) {
        File proofDir = new File(directory, "scripts");
        return new File(proofDir, Util.maskFileName(pvcIdentifier) + ".script");
    }

    /**
     * Load an alternative version of the project (which is saved as zip file).
     *
     * Future ....
     *
     * @param zipFile
     */
    public void loadProjectVersion(File zipFile) {
        throw new Error("Not yet");
    }


    /**
     * Return Proof object for a PVC if it exists, null otherwise
     *
     * @param pvcIdentifier
     * @return
     */
    public Proof getProofForPVC(String pvcIdentifier) {
        return getAllProofs().get(pvcIdentifier);
    }

    public Map<String, Proof> getAllProofs() {
        return Collections.unmodifiableMap(proofs);
    }

    /**
     * Save the whole Project contents
     */
    public void saveProject() throws IOException {
        for (Map.Entry<String, Proof> pvcProofEntry : proofs.entrySet()) {
            String pvcName = pvcProofEntry.getKey();
            Proof proof = pvcProofEntry.getValue();
            saveProofScriptForPVC(pvcName, proof);
        }

    }

    public void saveProofScriptForPVC(String pvcIdentifier, Proof proof) throws IOException {
        File scriptFile = getScriptFileForPVC(pvcIdentifier);
        saverHelper(scriptFile.getPath(), proof.getScript());
    }

    /**
     * Get the plain PVCs as Map from pvcName -> PVC object
     *
     * @return
     */
    public Map<String, PVC> getPVCByNameMap() {
        return this.project.getValue().getPVCByNameMap();
    }

    /**
     * Save project to a zipfile
     */
    public void saveProjectVersion() throws IOException {
        saveProject();
    }

    /**
     * Add a filehook for saving content in case of project saving
     *
     * @param filename to which file the content shoudl be saved
     * @param content  Supplier funtion from which content can be retrieved
     */
    public void addFileHook(String filename, Supplier<String> content) {
        this.fileHooks.putIfAbsent(filename, content);
    }

    /**
     * Remove file hook
     *
     * @param filename
     */
    public void removeFileHook(String filename) {
        this.fileHooks.remove(filename);
    }

    public Project getProject() {
        return project.getValue();
    }

    /* *
     * Save content to script file for pvc
     * @param pvc
     * @param content
     * @throws IOException
     */
 /*   public void saveToScriptFile(String pvc, String content) throws IOException {
        String scriptFilePath = project.get().getBaseDir().getAbsolutePath() + File.separatorChar + pvc + ".script";
        saverHelper(scriptFilePath, content);

    }*/

    /* REVIEW I propose: static method
        Path path = Paths.get(pathToFile);
        if (!Files.exists(path)) {
            Files.createFile(path);
        }

        try(Writer writer = Files.newBufferedWriter(path)) {
            writer.write(content);
            writer.flush();
        }
     */
    private void saverHelper(String pathToFile, String content) throws IOException {
        Path path = Paths.get(pathToFile);
        Writer writer;
        if (Files.exists(path)) {
            writer = Files.newBufferedWriter(path);
        } else {
            Files.createDirectories(path.getParent());
            Path file = Files.createFile(path);
            writer = Files.newBufferedWriter(file);
        }
        writer.write(content);
        writer.flush();
        writer.close();
    }

//    public File getConfigFile() {
//        return configFile;
//    }

//    public void setConfigFile(File configFile) {
//        this.configFile = configFile;
//    }

    /**
     * Return  all PVCs for the loaded project
     *
     * @return PVCGroup that is the root for all PVCs of the loaded project
     */
    public PVCGroup getPVCGroup() {
        return this.getProject().getAllPVCs();
    }

    public String getConfigFilename() {
        return configFilename;
    }

    public File getDirectory() {
        return directory;
    }
}
