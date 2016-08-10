package edu.kit.iti.algover.project;

import edu.kit.iti.algover.settings.ProjectSettings;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * Class for building a project in AlgoVer
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 * Created by sarah on 8/3/16.
 */
public  class ProjectBuilder {
    /**
     * List of all files in the project directory
     */
    private  File[] allFilesinDir;

    /**
     * All imported libraries
     */
    private List<File> libraries;

    /**
     * All Dafnyfiles in the project directory
     */
    private List<File> dafnyFiles;

    /**
     * The project's directory location
     */
    private File dir;

    /**
     * All compilationunits of a project
     *
     */
    private List<DafnyCompilationUnit> cpus;


    /**
     * Setting of project
     */
    private ProjectSettings settings;


    public File getScript() {
        return script;
    }

    /**
     * The script of the project
     *
     */
    private File script;

    public ProjectSettings getSettings() {
        return settings;
    }

    public List<File> getLibraries() {
        return libraries;
    }

    public List<File> getDafnyFiles() {
        return dafnyFiles;
    }

    public File getDir() {
        return dir;
    }

    public List<DafnyCompilationUnit> getCpus() {
        return cpus;
    }

    public ProjectBuilder setLibraries(List<File> libraries) {
        this.libraries = libraries;
        return this;
    }

    public ProjectBuilder setDafnyFiles(List<File> dafnyFiles) {
        this.dafnyFiles = dafnyFiles;
        return this;
    }

    public ProjectBuilder setDir(File dir) {
        this.dir = dir;
        return this;
    }

    public ProjectBuilder setCpus(List<DafnyCompilationUnit> cpus) {
        this.cpus = cpus;
        return this;
    }

    public ProjectBuilder setSettings(ProjectSettings settings) {
        this.settings = settings;
        return this;
    }

    public ProjectBuilder setScript(File script) {
        this.script = script;
        return this;
    }

    /**
     * Responsible for building project
     */
    public ProjectBuilder(){


    }

    /**
     * Build project. Handle calling parsers and calling DafnyDecl Builder
     * @param dir of project
     * @return Project Object
     */
    public Project buildProject(File dir){
        //setDir(dir);

        //find files
        //call script parser
        //set settings
        //call file parser get dafnytree
        //call compilationunit nbuilder with decltree and lib references
        //get compilationunit
        return new Project(this);
    }

    /**
     * Searches project directory for file ending with .script
     * At the moment no error handling if more than one script file exists
     * Creates a new file named project.script if no file exists, its not saved to directory yet
     * @return Scriptfile
     */
//    private  File findScriptFile(File dir){
//        for (File f : getAllFilesinDir()) {
//            if(f.getName().endsWith(".script")) {
//                System.out.println(f.getName());
//                return f;
//            }
//        }
//        System.out.println("No script file exists, creating one in the directory and will be called project.script");
//        createNewScriptFile(dir);
//        return new File("project.script");
//
//    }

}
