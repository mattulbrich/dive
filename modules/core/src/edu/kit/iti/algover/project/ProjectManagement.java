package edu.kit.iti.algover.project;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import javafx.beans.property.SimpleObjectProperty;

import java.io.File;
import java.util.HashMap;

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


    private HashMap<String, Proof> allProofs;

    /**
     * Load a Project from a given config file and set the property for the project
     *
     * @param config File
     */
    public void loadProject(File config) {
        this.configFile = config;
        Project p = null;
        try {
            p = ProjectFacade.getInstance().buildProjectWithConfigFile(config);
            this.allPVCs = p.generateAndCollectPVC();
            this.setProject(p);
        } catch (Exception e) {
            System.out.println("Project from " + config.getName() + " could not be built");
            e.printStackTrace();
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

    public HashMap<String, Proof> getAllProofs() {
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
