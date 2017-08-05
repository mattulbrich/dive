package edu.kit.iti.algover.project;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.proof.PVCGroup;
import javafx.beans.property.SimpleObjectProperty;

import java.io.File;

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

}
