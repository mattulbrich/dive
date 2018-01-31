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
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.util.FileUtil;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Util;
import javafx.beans.property.SimpleObjectProperty;
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
public class ProjectManager {

    private static final String CONFIG_DEFAULT_NAME = ProjectBuilder.CONFIG_DEFAULT_FILENAME;

    /**
     * Property for project
     */
    private final Project project;

    /**
     * Map from PVC identifiers to corr. proofs.
     */
    private Map<String, Proof> allProofs;

    // REVIEW Documentation?
    private Map<String, Supplier<String>> fileHooks = new HashMap<>();

    /**
     * Build a new Project by parsing the config file and performing symbolic execution
     *
     * @param directory      the directory where the problem resides in
     * @param configFilename the filename of the configuration within this directory
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public ProjectManager(File directory, String configFilename) throws FormatException, DafnyParserException, IOException, DafnyException {
        this.project = buildProject(directory, configFilename);

        generateAllProofObjects();
        for (String s: this.getPVCByNameMap().keySet()) {
            initializeProofDataStructures(s);
        }
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


    /**************************************************************************************************
     *
     *                                        Load
     *
     *************************************************************************************************/

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
            // TODO Is it wise to only return the first exception?
            throw exceptions.get(0);
        }

        return result;
    }

    /**
     * Generate all proof objects for all available PVCs in allPVCs
     * The data strcutures of teh Proof object are null after this method call
     */
    private void generateAllProofObjects() throws IOException {
        allProofs = new HashMap<>();
        for (String pvc : getPVCByNameMap().keySet()) {
            Proof p = new Proof(pvc);
            allProofs.put(pvc, p);
        }
    }

    /**
     * Add available data to proof objects by searching proof scripts and adding
     * the parsed script tree and setting the proof root.
     *
     * @param pvcName name of the PVC to be initialized
     * @throws IOException if reading the file fails. NB: If the proof file does
     *                     not exist, no exception is thrown.
     */
    private void initializeProofDataStructures(String pvcName) throws IOException {
        Proof p = allProofs.get(pvcName);
        PVC pvcObject = getPVCByNameMap().get(pvcName);
        p.setProofRoot(new ProofNode(null, null, null, pvcObject.getSequent(), pvcObject));

        try {
            // Either the script file can be loaded, then that file is used for
            // building the proof object
            findAndParseScriptFileForPVC(pvcName);
        } catch (FileNotFoundException e) {
            // REVIEW MU: What does "stubbed" mean?
            // Or the proof object is simply stubbed
        }

        buildIndividualInterpreter(p);
    }

    /**
     * Find and parse script file for pvc. Set the ASTroot in the corresponding
     * proof object.
     *
     * @param pvc
     * @return TODO should return ScriptAST
     */

    public void findAndParseScriptFileForPVC(String pvc) throws IOException {

        //find file on disc
        File proofDir = new File(project.getBaseDir(), "proofs");
        File scriptFile = FileUtil.findFile(proofDir, Util.maskFileName(pvc) + ".script");

        if (scriptFile.exists()) {
            ProofScript root = Facade.getAST(scriptFile);
            Proof proof = allProofs.get(pvc);
            if (proof == null) {
                // REVIEW: Can that ever be null?
                proof = new Proof(pvc);
            }
            proof.setScript(root.getBody());
            proof.setProofStatus(ProofStatus.SCRIPT_PARSED);
            allProofs.putIfAbsent(pvc, proof);
        } else {
            throw new FileNotFoundException("File " + scriptFile + " cannot be found");
        }

    }

    /**
     * Build the individual interpreter for a proof object and set it
     *
     * @param p Proofobject for which the interpreter needs to be built
     *
     */
    protected void buildIndividualInterpreter(Proof p) {

        InterpreterBuilder ib = new InterpreterBuilder();
        if (p.getScript() == null) {
            Interpreter i = ib
                    .setProofRules(this.project.getAllProofRules())
                    .startState(p.getProofRoot())
                    .build();
            p.setInterpreter(i);
        } else {
            Interpreter i = ib.startWith(p.getScript())
                    .setProofRules(this.project.getAllProofRules())
                    .startState(p.getProofRoot())
                    .build();
            p.setInterpreter(i);
        }
    }

    /**
     * Load an alternative version of the project (which is saved as zip file)
     *
     * @param zipFile
     */
    public void loadProjectVersion(File zipFile) {

    }


    /**
     * Return Proof object for a PVC if it exists, null otherwise
     *
     * @param pvcIdentifier
     * @return
     */
    public Proof getProofForPVC(String pvcIdentifier) {
        return getAllProofs().getOrDefault(pvcIdentifier, null);
    }

    /**************************************************************************************************
     *
     *                                        Save
     *
     *************************************************************************************************/

    public Map<String, Proof> getAllProofs() {
        return allProofs;
    }



    /**
     * Save the whole Project contents
     */
    public void saveProject() throws IOException {
        for (Map.Entry<String, Proof> pvcProofEntry : allProofs.entrySet()) {
            String pvcName = pvcProofEntry.getKey();
            Proof proof = pvcProofEntry.getValue();
            String content = "";
           /* if (proof.getScriptRoot() != null) {
                ASTNode script = proof.getScriptRoot();
                content =
                    "auto;\n" +
                            "cases{\n" +
                            "    case match '1==2'{\n" +
                            "        auto;\n" +
                            "    }\n" +
                            "    default:{\n" +
                            "        auto;\n" +
                            "    }\n" +
                            "}";
            }*/
            //ScriptHelper.visitASTNODE -> String content
            //saveToScriptFile(pvcName, content);
        }

        // REVIEW: When using saveHelper use "Util.maskFileName(pvcName)" here.

    }

    /**
     * Get the plain PVCs as Map from pvcName -> PVC object
     *
     * @return
     */
    public Map<String, PVC> getPVCByNameMap() {
        return this.project.getPVCByNameMap();
    }



    /**
     * Save content to Dafny file
     *
     * @param file    to save content to
     * @param content content to save
     */
/*    public void saveToDfyFile(File file, String content) throws IOException {
        saverHelper(file.getAbsolutePath(), content);
    }
*/
    /**
     * Save project to a zipfile
     */
    public void saveProjectVersion() throws IOException {
        saveProject();
    }


    /**************************************************************************************************
     *
     *                                        Getter and Setter
     *
     *************************************************************************************************/

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
        return project;
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
        return this.project.getAllPVCs();
    }



}
