package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.gui.MainWindow;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.ProjectTreeBuilder;
import edu.kit.iti.algover.project.Project;

import javax.swing.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeListenerProxy;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.FileNotFoundException;

/**
 * SpiderPattern class
 * Manages ditsribution of data to show in GUI components
 *
 * This object holds all relevant information to create the project.
 * It also holds the reference to the projectfacade, such that all communication to the core has to be performed via GUICenter
 *
 * All relevant listeners should register here
 *
 *
 * Created by sarah on 8/3/16.
 */


public class GUICenter {


     /**
     * Boolean property that is set, if a project is completely loaded and the project object is returned
     *
     */
    public static final String PROJECT_LOADED = "project_loaded";

    /**
     * Boolean property that is set, if the dafny source has been edited
     *
     */
    public static final String DAFNY_SOURCE_CHANGED = "dafny_source_changed";

    public static  final String LOGICAL_VIEW_CHANGED = "logical_view_changed";

    public static final String PVC_STATUS_CHANGED = "pvc_status_changed";

    public static final String PORERTY_CHANGED = "property_changed";

    public Project getLoadedProject() {
        return loadedProject;
    }

    public void setLoadedProject(Project loadedProject) {
        this.loadedProject = loadedProject;
    }

    //Loaded project object
    private Project loadedProject;

    private File selectedProjectDir;

    private MainWindow mainwindow;

    public ProjectTree getProjectTreeModel() {
        return projectTreeModel;
    }

    private ProjectTree projectTreeModel;

    public MainWindow getMainwindow() {
        return mainwindow;
    }

    public ProjectFacade getFacade() {
        return facade;
    }

    private ProjectFacade facade;

    public GUICenter(MainWindow window){
        this.mainwindow = window;
        this.facade = ProjectFacade.getInstance();
    }


    public void setSelectedProjectDir(File parentFile) {
        this.selectedProjectDir = parentFile;
        System.out.println("Set selected Project directory");
    }

    public void loadSelectedProject(){
        if(selectedProjectDir == null){
            JOptionPane.showMessageDialog(mainwindow,
            "You have to select the project's directory first.",
            "Project Directory",
            JOptionPane.ERROR_MESSAGE);

        }else{
            try{
                this.loadedProject = facade.buildProject(this.selectedProjectDir);
                ProjectTreeBuilder builder = new ProjectTreeBuilder();

                ProjectTree pTree = builder.buildProject(this.loadedProject);
                if (pTree == null) {
                    JOptionPane.showMessageDialog(mainwindow,
                            "Could not build project " + this.selectedProjectDir.toString(),
                            "Project Directory",
                            JOptionPane.ERROR_MESSAGE);
                } else {
                    this.projectTreeModel = pTree;
                    System.out.println("Project " + loadedProject.getScript().getAbsolutePath() + " is loaded");
                }
            }catch (FileNotFoundException e){
                JOptionPane.showMessageDialog(mainwindow,
                        "Could not build project " + this.selectedProjectDir.toString(),
                        "Project Directory",
                        JOptionPane.ERROR_MESSAGE);
            }catch (Exception ex){
                JOptionPane.showMessageDialog(mainwindow,
                        "Could not build project " + this.selectedProjectDir.toString(),
                        "Project Directory",
                        JOptionPane.ERROR_MESSAGE);
            }

        }
    }
}
