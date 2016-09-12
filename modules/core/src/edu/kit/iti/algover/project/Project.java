package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.settings.ProjectSettings;

import java.io.File;


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
    private final File script;

    /**
     * List containing references to all problem files
     */
    private final List<File> dafnyFiles;

    public List<DafnyFunction> getFunctions() {
        return functions;
    }

    public List<DafnyMethod> getMethods() {
        return methods;
    }

    public List<DafnyClass> getClasses() {
        return classes;
    }

    public List<File> getLibraries() {
        return libraries;
    }

    public ProjectSettings getSettings() {
        return settings;
    }

    public List<File> getDafnyFiles() {
        return dafnyFiles;
    }

    public File getScript() {
        return script;
    }

    /**
     * Settings of Project
     */
    private final ProjectSettings settings;

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
        this.settings = pBuilder.getSettings();
//        this.compilationUnits = pBuilder.getCpus();
        this.dafnyFiles = pBuilder.getDafnyFiles();
//        this.pathOfProjectDirectory = pBuilder.getDir();
        this.libraries = pBuilder.getLibraries();
      //  this.elementsOfProject = buildDafnyDecl();
        this.script = pBuilder.getScript();
        this.classes = pBuilder.getClasses();
        this.functions = pBuilder.getFunctions();
        this.methods = pBuilder.getMethods();
    }

    public String toString(){

        String s = "Project\n";
        s+= "imports ";
        if(libraries.size() != 0) {
            for (File f : libraries) {
                s += f.getName()+"\n";
            }
        }
        if(classes.size() != 0) {
            s += "with ";
            s += this.classes.size();
            s += " classe(s): \n";
            for (DafnyClass dClass : this.classes) {
                s += dClass.toString();
            }
        }else{
            s += "with ";
            s += this.methods.size();
            s += " method(s): \n";
            for (DafnyMethod m : this.methods) {

                s += m.toString();
            }
        }
        return s;

    }

}
