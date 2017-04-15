/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyTreeToDeclVisitor;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.script.ScriptFileParser;
import edu.kit.iti.algover.script.ScriptParser;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FileUtil;
import org.antlr.runtime.RecognitionException;

import java.io.*;
import java.util.LinkedList;
import java.util.List;

/**
 * Class for building a project in AlgoVer
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 * Created by sarah on 8/3/16.
 */
public class ProjectBuilder {

    /**
     * All imported libraries
     */
    private List<File> libraries;

    /**
     * The script of the project
     */
    private File script;

    private List<DafnyFunction> functions;

    private List<DafnyClass> classes;

    private List<DafnyMethod> methods;

    /**
     * All Dafnyfiles in the project directory
     */
    private List<File> dafnyFiles;

    /**
     * The project's directory location
     */
    private File dir;

    /**
     * Setting of project
     */
    private ProjectSettings settings;

    /**
     * Responsible for building project
     */
    public ProjectBuilder() {

        this.methods = new LinkedList<>();
        this.functions = new LinkedList<>();
        this.classes = new LinkedList<>();

    }

    public File getScript() {
        return script;
    }

    public ProjectBuilder setScript(File script) {
        this.script = script;
        return this;
    }

    public ProjectSettings getSettings() {
        return settings;
    }

    public ProjectBuilder setSettings(ProjectSettings settings) {
        this.settings = settings;
        return this;
    }

    public List<File> getLibraries() {
        return libraries;
    }

    public ProjectBuilder setLibraries(List<File> libraries) {
        this.libraries = libraries;
        return this;
    }

    public List<File> getDafnyFiles() {
        return dafnyFiles;
    }

    public ProjectBuilder setDafnyFiles(List<File> dafnyFiles) {
        this.dafnyFiles = dafnyFiles;
        return this;
    }

    public File getDir() {
        return dir;
    }


    public ProjectBuilder setDir(File dir) {
        this.dir = dir;
        return this;
    }

    // REVIEW Why does this method not throw exceptions? This here does not allow
    //  for error messages in GUI e.g.
    /**
     * Parse dafnyfile
     *
     * @param file dafnyfile
     * @return parsed file as DafnyTree
     */
    public DafnyTree parseFile(File file) {
        DafnyTree t = null;
        try {
            FileInputStream inputStream = new FileInputStream(file);
            t = DafnyFileParser.parse(inputStream);
        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            System.out.println("Could not load problem");
            e.printStackTrace();
        }
        return t;
    }

    // REVIEW This method seems to break the builder pattern. Is this class acc. to this pattern?
    // If not, please rename it.
    // REVIEW Could there not be two projects in the same directory tree?
    // (Perhaps several proof trials with different sttings?)
    /**
     * Build project. Handle calling parsers and calling DafnyDecl Builder
     *
     * @param dir of project
     * @return Project Object
     */
    public Project buildProject(File dir) throws FileNotFoundException, Exception {
        this.setDir(dir);
        ProjectSettings settings = new ProjectSettings();
        this.setSettings(settings); //default settings
        //find files

        File scriptFile = null;

        scriptFile = FileUtil.findFile(dir, "project.script");

        // REVIEW why is there a public setScript method if this is set here?
        if (scriptFile != null) {
            this.setScript(scriptFile);
        } else {
            throw new Exception("Could not build project");
        }
        //call script parser and get parsed Script
        ScriptTree parsedScript = parseScriptFile(this.getScript());
        // REVIEW caution this value might be null. Why not use exceptions?

        // REVIEW is there guarantee that settings is different from null?
        //extract settings from ScriptTree and change settings in data structure
        extractSettings(parsedScript.getFirstChildWithType(ScriptParser.SETTINGS));
        //extract dafnyfiles into datastructure
        extractDafnyFileNames(parsedScript.getFirstChildWithType(ScriptParser.IMPORT));

        // REVIEW why are there public methods to set library and import files
        // if this is extracted here?
        //extract Dafnylib files into datastructure
        extractDafnyFileNames(parsedScript.getFirstChildWithType(ScriptParser.LIBRARY));
        //parse DafnyFiles

        for (File file: this.getDafnyFiles()) {
            DafnyTree parsed = parseFile(file);
            // REVIEW This may be null and the following does not take care of that.
            // Why not use DafnyFileParser.parse?
            DafnyTreeToDeclVisitor visitor = new DafnyTreeToDeclVisitor(this, file);
            visitor.visit(dir.getName(), parsed);
        }

        return new Project(this);
    }

    /**
     * Extract DafnyFilenames from a subtree that has import as root and create new File with current Directory
     */
    public void extractDafnyFileNames(ScriptTree t) {
        List<ScriptTree> dafnyF = t.getChildrenWithType(ScriptParser.FILE);
        List<File> dafnyFilesTemp = new LinkedList<>();
        for (ScriptTree tree : dafnyF) {
            File f = new File(this.dir + File.separator + tree.getChild(0).getText() + tree.getChild(1).getText());
            dafnyFilesTemp.add(f);
           // System.out.println(t.getText()+" "+f.getName());

        }
        switch (t.getType()) {
            case ScriptParser.IMPORT:
                this.setDafnyFiles(dafnyFilesTemp);
             //   System.out.println("Set Dafnyfiles");
                break;
            case ScriptParser.LIBRARY:
                this.setLibraries(dafnyFilesTemp);
              //  System.out.println("Set Lib files");
                break;
            default:
              //  System.out.println("Type for files unknown");
        }
    }

    // REVIEW like above. Why are all exceptions discarded?
    /**
     * Parse Script File and return Tree to traverse
     *
     * @param script
     * @return
     */
    public ScriptTree parseScriptFile(File script) {
        ScriptTree t = null;
        try {

            InputStream scriptStream = FileUtil.readFile(script);
            t = ScriptFileParser.parse(scriptStream);


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file "+script.toString());
            e.printStackTrace();
        } catch (RecognitionException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (Exception e) {
            e.printStackTrace();
        }
        // REVIEW: Why are there 4 handlers with the same code? The last
        //  handles it as well as all the ones before.
        return t;

    }



    public void addFunction(DafnyFunction func) {
        this.functions.add(func);
   /*     if(currentClassBuilder != null)
            currentClassBuilder.addFunction();*/
    }

    /**
     * Hier müssen noch die Methoden extrahoert werden evtl.
     * @param dafnyClass
     */
    public void addClass(DafnyClass dafnyClass) {
        this.classes.add(dafnyClass);
    }

    public void addMethod(DafnyMethod meth) {
        this.methods.add(meth);
    }

    public List<DafnyClass> getClasses() {
        return this.classes;
    }

    public List<DafnyFunction> getFunctions() {
        return this.functions;
    }

    public List<DafnyMethod> getMethods() {
        return this.methods;
    }

    /**
     * Ectract Settings and add them to settingsobject (maybe refactor to settings class)
     * @param t ScriptTree with root node Settings
     */
    public void extractSettings(ScriptTree t){
       List<ScriptTree> sets = t.getChildrenWithType(ScriptParser.SET);
        for (ScriptTree tr: sets) {
            if(tr.getText().equals("dafny_timeout")){
                this.settings.setValue(ProjectSettings.DAFNY_TIMEOUT, tr.getChild(0).toString());
            }
            if(tr.getText().equals("key_timeout")){
                 this.getSettings().setValue(ProjectSettings.KEY_TIMEOUT, tr.getChild(0).toString());
            }

        }
    }

}
