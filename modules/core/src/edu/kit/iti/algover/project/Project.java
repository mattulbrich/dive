package edu.kit.iti.algover.project;

import java.io.File;


import java.util.LinkedList;
import java.util.List;


/**
 * Class representing a project, that contains all relevant information for a project that should be verified
 * Created by sarah on 8/3/16.
 */
public class Project {

    /**
     * Path of projects directory
     */
    private File pathOfprojectDirectory;

    /**
     * Script file
     */
    private File script;

    /**
     * List containing references to all problem files
     */
    private LinkedList<File> problemFiles;
    //TODO: Settings for project


    /**
     * Reference to all elements of the project: classes, methods, functions, classfields
     */
    private List<DafnyDecl> elementsOfProject;
    /**
     * Retrieve path of directory of project
     * @return
     */

    public File getPathOfprojectDirectory() {
        return pathOfprojectDirectory;
    }

    public void setPathOfprojectDirectory(File pathOfprojectDirectory) {
        this.pathOfprojectDirectory = pathOfprojectDirectory;
    }

    public File getScript() {
        return script;
    }

    public void setScript(File script) {
        this.script = script;
    }

    public LinkedList<File> getProblemFiles() {
        return problemFiles;
    }

    public void setProblemFiles(LinkedList<File> problemFiles) {
        this.problemFiles = problemFiles;
    }

    public Project(File projectPath, File script, LinkedList<File> problemFiles){
        this.setPathOfprojectDirectory(projectPath);
        this.setScript(script);
        this.setProblemFiles(problemFiles);

    }

    /**
     * Call to the parser, to extract the DafnyDecls.
     */
    public void parseFiles(){

    }


}
