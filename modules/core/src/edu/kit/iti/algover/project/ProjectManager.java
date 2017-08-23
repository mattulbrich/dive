package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.parser.Facade;
import javafx.beans.property.SimpleObjectProperty;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

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

    private PVCGroup allPVCs;

    private Map<String, PVC> allStrippedPVCs;

    private Map<String, Proof> allProofs;

    private InterpreterBuilder ib = new InterpreterBuilder();



    /**************************************************************************************************
     *
     *                                        Load
     *
     *************************************************************************************************/

    /**
     * Load a Project from a given config file and set the property for the project
     *
     * @param config File
     */
    public void loadProject(File config) throws Exception {
        this.configFile = config;
        Project p = null;
        p = buildProject(config.toPath());
        this.allPVCs = p.generateAndCollectPVC();
        this.allStrippedPVCs = p.getPvcCollectionByName();
        this.setProject(p);
        generateAllProofObjects();

    }

    /**
     * Build a new Project
     *
     * @param pathToConfig to config file
     * @return new Project object
     * //TODO Create Parsing Exception for config file
     */
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
     */
    private void generateAllProofObjects() {
        allProofs = new HashMap<>();
        for (String pvc : allStrippedPVCs.keySet()) {
            Proof p = new Proof(pvc);
            //load scriptfile for Proof if existing+parse it
            allProofs.put(pvc, p);
        }
    }

    /**
     * Find and parse script file for pvc. Set the ASTroot in the corresponding proof object
     *
     * @param pvc
     * @return TODO should return ScriptAST
     */

    public void findAndParseScriptFile(String pvc) throws IOException {
        String filePath = project.get().getBaseDir().getAbsolutePath() + pvc + ".script";
        //find file on disc
        Path p = Paths.get(filePath);
        ASTNode root = Facade.getAST(p.toFile());
        Proof proof = allProofs.get(pvc);
        if (proof == null) {
            proof = new Proof(pvc);
        }
        proof.setScriptRoot(root);

        //proof.setInterpreter();
        allProofs.putIfAbsent(pvc, proof);

    }

    /**
     * Load an alternative version of the project (which is saved as zip file)
     *
     * @param zipFile
     */
    public void loadProjectVersion(File zipFile) {

    }

    /**
     * Set all proofs to DIRTY
     */
    public void invalidateAllProofs() {
        for (String pvc : allStrippedPVCs.keySet()) {
            invalidateProofForPVC(pvc);
        }
    }

    /**
     * Invalidate Proof for a pvc
     *
     * @param name pvcidentifier
     */
    public void invalidateProofForPVC(String name) {
        Proof pr = getProofForPVC(name);
        if (pr != null) {
            pr.setProofStatus(ProofStatus.DIRTY);
        }

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
     * Replay all available proofs
     */
    public void replayAllProofs() throws IOException {
        saveProject();
        //save everything before replay
        for (Proof proof : allProofs.values()) {
            proof.replay();
        }

    }

    /**
     * Save the whole Project contents
     */
    public void saveProject() throws IOException {
        for (Map.Entry<String, Proof> pvcProofEntry : allProofs.entrySet()) {
            String pvcName = pvcProofEntry.getKey();
            Proof proof = pvcProofEntry.getValue();
            String content = "";
            if (proof.getScriptRoot() != null) {
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
            }
            //ScriptHelper.visitASTNODE -> String content
            saveToScriptFile(pvcName, content);
        }

    }

    /**
     * Save content to script file for pvc
     * @param pvc
     * @param content
     * @throws IOException
     */
    public void saveToScriptFile(String pvc, String content) throws IOException {
        String scriptFilePath = project.get().getBaseDir().getAbsolutePath() + File.separatorChar + pvc + ".script";
        saverHelper(scriptFilePath, content);

    }

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
    public void saveToDfyFile(File file, String content) throws IOException {
        saverHelper(file.getAbsolutePath(), content);
    }

    /**
     * Save project to a zipfile
     */
    public void saveProjectVersion() throws IOException {
        saveProject();
    }

    /**
     * Return all available rules for project
     *
     * @return
     */
    public Collection<ProofRule> getAllRules() {
        //get rules form project
        return Collections.EMPTY_LIST;
    }

    /**************************************************************************************************
     *
     *                                        Getter and Setter
     *
     *************************************************************************************************/
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


}
