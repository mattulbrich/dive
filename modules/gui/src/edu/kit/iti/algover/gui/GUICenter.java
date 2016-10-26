package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.model.ProjectTreeBuilder;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofManagement;

import javax.swing.*;
import javax.swing.tree.TreePath;
import java.awt.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.FileNotFoundException;

/**
 * SpiderPattern class
 * Manages ditsribution of data to show in GUI components
 * <p>
 * This object holds all relevant information to create the project.
 * It also holds the reference to the projectfacade, such that all communication to the core has to be performed via GUICenter
 * <p>
 * All relevant listeners should register here
 * <p>
 * <p>
 * Created by sarah on 8/3/16.
 */


public class GUICenter {



    private PVC selectedPVCForDetailView;


    private ProofManagement pm;
    //core counterpart for communcation
    private ProjectFacade facade;


    //GUI model of project
    private ProjectTree selectedProjectSubTree;

    //Loaded project object
    private Project loadedProject;

    //selected project directory
    private File selectedProjectDir;

    //mainwindow instance
    private MainWindow mainwindow;


    //selected project leaf
    private CustomLeaf selectedLeaf;


    //path to selected subtree
    private TreePath selectedPath;
    /**
     * model of project
     */
    private ProjectTree projectTreeModel;


    private File loadedDafnySrc;
    /**
     * Property that is set, if a project is completely loaded and the project object is returned
     */
    public static final String PROJECT_LOADED = "project_loaded";

    /**
     * Property that is set, if the dafny source has been edited
     */
    public static final String DAFNY_SOURCE_CHANGED = "dafny_source_changed";

    public static final String LOGICAL_VIEW_CHANGED = "logical_view_changed";

    public static final String PVC_STATUS_CHANGED = "pvc_status_changed";

    //public static final String PROPERTY_CHANGED = "property_changed";

    /**
     * PVCs are generated and ready to display
     */

    public static final String PVCS_GENERATED = "pvcs_generated";
    /**
     * new subtree selected
     */
    public static final String SUBTREE_SELECTION = "subtree_selection";

    /**
     * new project directory set
     */

    public static final String PROJECT_DIR_CHANGED = "project_directory_changed";

    /**
     * project tree model has changed
     */
    public static final String PROJECT_TREE_MODEL_CHANGED = "project_tree_model_changed";

    /**
     * Selected leaf to load
     */
    public static final String LEAF_TO_LOAD = "leaf_to_load_selected";


    /**
     * Selected PVC for DetailView
     *
     */
    public static final String PVC_FOR_DETAIL = "pvc_for_detail";
    /**
     * Constructor
     *
     * @param window
     */
    public GUICenter(MainWindow window) {
        this.mainwindow = window;
        this.facade = ProjectFacade.getInstance();
    }


    private PropertyChangeSupport changes = new PropertyChangeSupport(this);

    /**
     * Propertychangelistener list
     *
     * @param l
     */
    public void addPropertyChangeListener(PropertyChangeListener l) {
        changes.addPropertyChangeListener(l);
    }

    public void removePropertyChangeListener(PropertyChangeListener l) {
        changes.removePropertyChangeListener(l);
    }


    //Getter & Setter

    public PVC getSelectedPVCForDetailView() {
        return selectedPVCForDetailView;
    }

    public void setSelectedPVCForDetailView(PVC selectedPVCForDetailView) {
        PVC oldPVC = this.getSelectedPVCForDetailView();
        this.selectedPVCForDetailView = selectedPVCForDetailView;
        changes.firePropertyChange(PVC_FOR_DETAIL, oldPVC, this.getSelectedPVCForDetailView());

    }

    public ProofManagement getProofManagement() {

        return pm;
    }


    /**
     * Proofmanagement with PVCs have been set
     * @param pm
     */
    public void setProofManagement(ProofManagement pm) {
        ProofManagement old = pm;
        this.pm = pm;
        changes.firePropertyChange(PVCS_GENERATED, old, this.getProofManagement());
    }

    public void setLoadedProject(Project loadedProject) {
        Project old = this.getLoadedProject();
        this.loadedProject = loadedProject;
        changes.firePropertyChange(PROJECT_LOADED, old, this.getLoadedProject());
    }

    public ProjectTree getSelectedProjectSubTree() {
        return selectedProjectSubTree;
    }

    //set the model for the projectTree
    public void setProjectTreeModel(ProjectTree projectTreeModel) {
        ProjectTree old = this.getProjectTreeModel();
        this.projectTreeModel = projectTreeModel;
        changes.firePropertyChange(PROJECT_TREE_MODEL_CHANGED, old, this.getProjectTreeModel());
    }

    /**
     * Set the reference to the ProjectTree in the GUI projectTreeModel that is currently selected by the user in the projectbrowser
     *
     * @param selectedProjectSubTree
     */
    public void setSelectedProjectSubTree(ProjectTree selectedProjectSubTree) {
        ProjectTree old = this.getSelectedProjectSubTree();
        this.selectedProjectSubTree = selectedProjectSubTree;
        changes.firePropertyChange(SUBTREE_SELECTION, old, this.getSelectedProjectSubTree());

    }

    public CustomLeaf getSelectedLeaf() {
        return selectedLeaf;
    }

    public void setSelectedLeaf(CustomLeaf selectedLeaf) {
        CustomLeaf old = this.getSelectedLeaf();
        this.selectedLeaf = selectedLeaf;

        changes.firePropertyChange(LEAF_TO_LOAD, old, this.getSelectedLeaf());
    }

    public File getSelectedProjectDir() {
        return selectedProjectDir;
    }


    public ProjectTree getProjectTreeModel() {
        return projectTreeModel;
    }


    public MainWindow getMainwindow() {
        return mainwindow;
    }

    public ProjectFacade getFacade() {
        return facade;
    }

    public Project getLoadedProject() {
        return loadedProject;
    }

    /**
     * Load selected Project and set fields
     * @param projectDir
     */
    public void loadProject(File projectDir) {

        setSelectedProjectDir(projectDir);
        loadSelectedProject();

        ProofManagement proofmgt = new ProofManagement(this.getLoadedProject(), this.getFacade());
        this.setProofManagement(proofmgt);
        System.out.println(this.getProofManagement().getProofverificationconditions().toString());


    }
    /**
     * Set the project directory that is selected by the user
     * @param parentFile
     */
    private void setSelectedProjectDir(File parentFile) {
        mainwindow.setEnabled(false);
        File old = this.getSelectedProjectDir();
        this.selectedProjectDir = parentFile;
        changes.firePropertyChange(PROJECT_DIR_CHANGED, old, this.getSelectedProjectDir());
        mainwindow.setEnabled(true);
       // System.out.println("Set selected Project directory");
    }

    public File getLoadedDafnySrc() {
        return loadedDafnySrc;
    }

    /**
     * Set the sourcefile for the currently selected projectsubtree
     * @param loadedDafnySrc
     */
    public void setLoadedDafnySrc(File loadedDafnySrc) {
        File old = this.getLoadedDafnySrc();
        this.loadedDafnySrc = loadedDafnySrc;
        changes.firePropertyChange(DAFNY_SOURCE_CHANGED, old, this.getLoadedDafnySrc());
    }

    /**
     * Load selected Project from directory, call to facade, retrieve project object
     */
    private void loadSelectedProject() {
        //Project old = this.getLoadedProject();
        if (selectedProjectDir == null) {
            JOptionPane.showMessageDialog(mainwindow,
                    "You have to select the project's directory first.",
                    "Project Directory",
                    JOptionPane.ERROR_MESSAGE);
        } else {
            try {
                this.setLoadedProject(facade.buildProject(this.selectedProjectDir));
            } catch (FileNotFoundException e) {
                JOptionPane.showMessageDialog(mainwindow,
                        "Could not find file " + this.selectedProjectDir.toString(),
                        "File not found",
                        JOptionPane.ERROR_MESSAGE);
            } catch (Exception ex) {
                JOptionPane.showMessageDialog(mainwindow,
                        "Could not build project " + this.selectedProjectDir.toString(),
                        "Project Directory",
                        JOptionPane.ERROR_MESSAGE);
            }

        }
    }

    public TreePath getSelectedPath() {
        return selectedPath;
    }

    public void setSelectedPath(TreePath selectedPath) {
        this.selectedPath = selectedPath;
    }
}
