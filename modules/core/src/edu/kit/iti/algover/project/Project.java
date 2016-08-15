package edu.kit.iti.algover.project;

import edu.kit.iti.algover.settings.ProjectSettings;

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

    //private final File pathOfProjectDirectory;

    /**
     * Script file
     */
    //private final File script;

    /**
     * List containing references to all problem files
     */
    //private final List<File> dafnyFiles;

    /**
     * Settings of Project
     */
    //private final ProjectSettings settings;

    /**
     * Reference to all elements of the project: classes, methods, functions, classfields
     */
    //private final List<DafnyDecl> elementsOfProject;

    /**
     * List of compilation units of project
     */
   // private final List<DafnyCompilationUnit> compilationUnits;

    /**
     * All imported libraries
     * DafnyLib
     */
    private List<File> libraries;

    private List<DafnyClass> classes;
    private List<DafnyMethod> methods;
    private List<DafnyFunction> functions;
    /**
     * Constructor can only be called using a ProjectBuilder
     * @param pBuilder
     */
    public Project(ProjectBuilder pBuilder){
 //       this.settings = pBuilder.getSettings();
//        this.compilationUnits = pBuilder.getCpus();
 //       this.dafnyFiles = pBuilder.getDafnyFiles();
//        this.pathOfProjectDirectory = pBuilder.getDir();
//        this.libraries = pBuilder.getLibraries();
      //  this.elementsOfProject = buildDafnyDecl();
  //      this.script = pBuilder.getScript();
        this.classes = pBuilder.getClasses();
        this.functions = pBuilder.getFunctions();
        this.methods = pBuilder.getMethods();
    }

    public String toString(){
        String s = "Project\n";
        s += "with classes: \n";
        for (DafnyClass dClass: this.classes) {
            s += dClass.toString();
        }

        return s;

    }

}
