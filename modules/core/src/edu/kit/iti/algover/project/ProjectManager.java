/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.util.FileUtil;
import edu.kit.iti.algover.util.Util;
import javafx.beans.property.SimpleObjectProperty;

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
 * Class handling project and proof management
 */
public class ProjectManager {


    /**
     * Reference to config file
     */
    private File configFile;

    /**
     * Property for Project
     */
    private SimpleObjectProperty<Project> project = new SimpleObjectProperty<>(null);

    /**
     * All PVCs of the loaded project
     */
    private PVCGroup allPVCs;


    /**
     * Map from PVC string to its PVC object
     */
    private Map<String, PVC> allStrippedPVCs;

    /**
     * Map from pvc string to it proof object
     */
    private Map<String, Proof> allProofs;


    private Map<String, Supplier<String>> fileHooks = new HashMap<>();


    /**************************************************************************************************
     *
     *                                        Load
     *
     *************************************************************************************************/

    /**
     * Load a Project from a given config file and set the property for the project
     * Generate all Proof objects and initialize their data structures
     *
     * @param config File
     */
    // REVIEW: please do not use "throws Exception"
    public void loadProject(File config) throws Exception {
        this.configFile = config;
        Project p = null;
        p = buildProject(config.toPath());
        this.allPVCs = p.generateAndCollectPVC();
        this.allStrippedPVCs = p.getPvcCollectionByName();
        this.setProject(p);
        generateAllProofObjects();

        this.allStrippedPVCs.forEach((s, pvc) -> {
            try {
                initializeProofDataStructures(s);
            } catch (IOException e) {
                e.printStackTrace();

            }
        });
    }

    /**
     * Build a new Project by parsing the config file and performing symbolic execution
     *
     * @param pathToConfig to config file
     * @return new Project object
     * //TODO Create Parsing Exception for config file
     */
    // REVIEW: please do not use "throws Exception"
    private static Project buildProject(Path pathToConfig) throws FileNotFoundException, Exception {
        Project p = null;
        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(pathToConfig.normalize().getParent().toAbsolutePath().toFile());
        pb.setConfigFilename(pathToConfig.getFileName().toString());
        pb.parseProjectConfigurationFile();
        p = pb.build();

        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor refResolver = new ReferenceResolutionVisitor(p, exceptions);
        refResolver.visitProject();

        TypeResolution typeRes = new TypeResolution(exceptions);
        typeRes.visitProject(p);

        return p;
    }

    /**
     * Generate all proof objects for all available PVCs in allPVCs
     * The data strcutures of teh Proof object are null after this method call
     */
    private void generateAllProofObjects() throws IOException {
        allProofs = new HashMap<>();
        for (String pvc : allStrippedPVCs.keySet()) {
            Proof p = new Proof(pvc);
            allProofs.put(pvc, p);
        }
    }

    /**
     * Add available data to proof objects by searching proof scripts and adding the parsed script tree and setting the proof root
     *
     * @param pvc
     * @throws IOException
     */
    protected void initializeProofDataStructures(String pvc) throws IOException {
        Proof p = allProofs.get(pvc);
        findAndParseScriptFile(Util.maskFileName(pvc));
        PVC pvcObject = allStrippedPVCs.get(pvc);
        p.setProofRoot(new ProofNode(null, null, null, pvcObject.getSequent(), pvcObject));
        buildIndividualInterpreter(p);


    }

    /**
     * Find and parse script file for pvc. Set the ASTroot in the corresponding proof object
     *
     * @param pvc
     * @return TODO should return ScriptAST
     */

    public void findAndParseScriptFile(String pvc) throws IOException {

        String filePath = project.get().getBaseDir().getAbsolutePath() + File.separatorChar + Util.maskFileName(pvc) + ".script";
        //find file on disc
        File scriptFile = FileUtil.findFile(project.get().getBaseDir(), Util.maskFileName(pvc) + ".script");

        if (scriptFile.exists()) {
            ProofScript root = Facade.getAST(scriptFile);
            Proof proof = allProofs.get(pvc);
            if (proof == null) {
                proof = new Proof(pvc);
            }
            proof.setScript(root.getBody());
            allProofs.putIfAbsent(pvc, proof);
        } else {
            throw new IOException("File " + filePath + " can not be found");
        }
           /* Proof proof = allProofs.get(pvc);
            proof.setScript(null);
            proof.setProofStatus(ProofStatus.NON_EXISTING);
            */


    }

    /**
     * Build the individual interpreter for a proof object and set it
     * @param p Proof for which the interpreter needs to be built
     */
    protected void buildIndividualInterpreter(Proof p) {

        InterpreterBuilder ib = new InterpreterBuilder();
        if (p.getScript() == null) {
            Interpreter i = ib
                    .setProofRules(this.project.get().getAllProofRules())
                    .startState(new GoalNode<ProofNode>(null, p.getProofRoot()))
                    .build();
            p.setInterpreter(i);
        } else {
            Interpreter i = ib.startWith(p.getScript())
                    .setProofRules(this.project.get().getAllProofRules())
                    .startState(new GoalNode<ProofNode>(null, p.getProofRoot()))
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
     * Save content to script file for pvc
     * @param content
     * @throws IOException
     */
 /*   public void saveToScriptFile(String pvc, String content) throws IOException {
        String scriptFilePath = project.get().getBaseDir().getAbsolutePath() + File.separatorChar + pvc + ".script";
        saverHelper(scriptFilePath, content);

    }*/

    /* REVIEW I propose:
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
        return project.get();
    }

    public void setProject(Project project) {
        this.project.set(project);
    }

    public SimpleObjectProperty<Project> projectProperty() {
        return project;
    }

    /**
     * Return  all PVCs for the loaded project
     *
     * @return PVCGroup that is the root for all PVCs of the loaded project
     */
    public PVCGroup getAllPVCs() {
        return this.allPVCs;
    }

    public File getConfigFile() {
        return configFile;
    }

    public void setConfigFile(File configFile) {
        this.configFile = configFile;
    }

    /**
     * Get the plain PVCs as Map from pvcName -> PVC object
     *
     * @return
     */
    // REVIEW: Please motivate why "stripped".
    public Map<String, PVC> getAllStrippedPVCs() {
        return allStrippedPVCs;
    }



}
