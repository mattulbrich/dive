package edu.kit.iti.algover.project;

import com.google.common.annotations.VisibleForTesting;
import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import javafx.beans.property.SimpleObjectProperty;

import java.io.File;
import java.io.IOException;
import java.io.Writer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

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
        p = ProjectFacade.getInstance().buildProjectWithConfigFile(config);
        this.allPVCs = p.generateAndCollectPVC();
        this.allStrippedPVCs = p.getPvcCollectionByName();
        this.setProject(p);
        generateAllProofObjects();

    }

    /**
     * Generate all proof objects for all available PVCs in allPVCs
     */
    @VisibleForTesting
    private void generateAllProofObjects() {
        allProofs = new HashMap<>();
        for (String pvc : allStrippedPVCs.keySet()) {
            Proof p = new Proof(pvc);
            //load scriptfile for Proof if existing+parse it
            allProofs.put(pvc, p);
        }
    }

    /**
     * Find and parse script file for pvc
     *
     * @param pvc
     * @return TODO should return ScriptAST
     */
    private void findAndParseScriptFile(String pvc) {
        String filePath = project.get().getBaseDir().getAbsolutePath() + File.separatorChar + pvc + ".script";
        //find file on disc
        //ScriptAST root = ScriptParser.parse(scriptFile)
    }

    /**
     * Load an alternative version of the project (which is saved as zip file)
     *
     * @param zipFile
     */
    public void loadProjectVersion(File zipFile) {

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
     * Set all proofs to DIRTY
     */
    public void invalidateAllProofs() {
        for (String pvc : allStrippedPVCs.keySet()) {
            invalidateProofForPVC(pvc);
        }
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

    /**************************************************************************************************
     *
     *                                        Save
     *
     *************************************************************************************************/


    /**
     * Save the whole Project contents
     */
    public void saveProject() throws IOException {
        for (Map.Entry<String, Proof> pvcProofEntry : allProofs.entrySet()) {
            String pvcName = pvcProofEntry.getKey();
            Proof proof = pvcProofEntry.getValue();
            //proof.getScriptASTNode
            //ScriptHelper.visitASTNODE -> String content
            String content = "DummyContent";
            saveToScriptFile(pvcName, content);
        }

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

    public Map<String, Proof> getAllProofs() {
        return allProofs;
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


}
