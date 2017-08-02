package edu.kit.iti.algover.project;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import javafx.beans.property.SimpleObjectProperty;

import java.io.File;
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
     * Genearte all proof objects for all available PVCs in allPVCs
     */
    private void generateAllProofObjects() {
        allProofs = new HashMap<>();
        for (String pvc : allStrippedPVCs.keySet()) {
            Proof p = new Proof();
            p.setProofStatus(ProofStatus.NOT_LOADED);
            p.setPvcName(pvc);
            allProofs.put(pvc, p);
        }


    }
    /**************************************************************************************************
     *
     *                                                  Getter and Setter
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
