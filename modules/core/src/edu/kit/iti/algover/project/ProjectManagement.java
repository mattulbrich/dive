package edu.kit.iti.algover.project;

import com.google.common.annotations.VisibleForTesting;
import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import javafx.beans.property.SimpleObjectProperty;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

/**
 * Class handling project and proof management
 */
public class ProjectManagement {


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
    public void replayAllProofs() {
        //save everything before replay
        for (Proof proof : allProofs.values()) {
            proof.replay();
        }

    }

    public void saveProject() {

    }

    public void saveToDfyFile(File file, String content) {

    }

    public void saveToScriptFile(String pvc, String content) throws IOException {
        String scriptFilePath = project.get().getBaseDir().getAbsolutePath() + File.separatorChar + pvc + ".script";
        FileWriter fileWriter = new FileWriter(scriptFilePath, false);
        fileWriter.write(content);
        fileWriter.flush();
        fileWriter.close();
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
