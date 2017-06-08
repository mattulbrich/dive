/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.settings.ProjectSettings;
import org.antlr.runtime.RecognitionException;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Class for building a Project object in AlgoVer
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 * @author S.Grebing
 * @author M. Ulbrich
 */

public class ProjectBuilder {

    /**
     * List of Dafnyfiles that serve as library files (i.e., no PVC is generated for them)
     */
    private final List<String> libraryFiles = new ArrayList<>();
    /**
     * All Dafnyfiles in the project directory
     */
    private final List<String> dafnyFiles = new ArrayList<>();
    private final Map<String, DafnyTree> dafnyTrees = new HashMap<>();
    /**
     * The project's directory location
     */
    private File dir;
    /**
     * The script of the project (will be replaced by an xml file with default name config.xml)
     */
    private String scriptFilename = "config.xml";
    /**
     * Setting of project
     */
    private ProjectSettings settings = new ProjectSettings();
    private List<DafnyFile> files;
    private List<DafnyMethod> methods;
    private List<DafnyFunction> functions;
    private List<DafnyClass> classes;

    public String getScriptFilename() {
        return scriptFilename;
    }

    public ProjectBuilder setScriptFilename(String scriptFile) {
        this.scriptFilename = scriptFile;
        return this;
    }

    public ProjectSettings getSettings() {
        return settings;
    }

    public ProjectBuilder setSettings(ProjectSettings settings) {
        this.settings = settings;
        return this;
    }

    public List<String> getLibraryFiles() {
        return libraryFiles;
    }

    public void addLibraryFile(String file) {
        libraryFiles.add(file);
    }

    public List<String> getDafnyFiles() {
        return dafnyFiles;
    }

    public void addDafnyFile(String file) {
        dafnyFiles.add(file);
    }

    public Map<String, DafnyTree> getDafnyTrees() {
        return dafnyTrees;
    }

    public void addDafnyTree(String filename, DafnyTree tree) {
        dafnyTrees.put(filename, tree);
    }

    public File getDir() {
        return dir;
    }


    public ProjectBuilder setDir(File dir) {
        this.dir = dir;
        return this;
    }


    /**
     * This method invokes the problemloader to oad and parse the project configuration file
     *
     * @throws IOException
     * @throws RecognitionException TODO error handling
     */
    public void parseProjectConfigurationFile() throws IOException, RecognitionException {

        File absolutePath = new File(this.getDir() + "/" + getScriptFilename());
        Configuration config = ProblemLoader.loadConfigFile(absolutePath);

        if (config.getDafnyFiles() != null) {
            config.getDafnyFiles().stream().forEach(file -> {
                this.addDafnyFile(file.getPath());
            });
        }
        if (config.getLibFiles() != null) {
            config.getLibFiles().stream().forEach(file -> {
                this.addLibraryFile(file.getPath());
            });
        }
        this.setSettings(config.getProjectSettings());
    }

    /**
     * Build the Project object with all resources
     *
     * @return Project
     * @throws IOException
     * @throws RecognitionException
     * @throws DafnyException
     */
    public Project build() throws IOException, RecognitionException, DafnyException, DafnyParserException {
        this.files = new ArrayList<>();
        this.methods = new ArrayList<>();
        this.functions = new ArrayList<>();
        this.classes = new ArrayList<>();

        // parse DafnyFile
        for (String file: this.getDafnyFiles()) {
            DafnyTree tree = DafnyFileParser.parse(new File(dir, file));
            parseFile(false, tree, file);
        }

        for (String file: this.getLibraryFiles()) {
            DafnyTree tree = DafnyFileParser.parse(new File(dir, file));
            parseFile(true, tree, file);
        }

        for (Map.Entry<String, DafnyTree> en : dafnyTrees.entrySet()) {
            parseFile(true, en.getValue(), en.getKey());
        }

        return new Project(this);
    }

    /**
     * Parse a Dafny File
     *
     * @param inLib
     * @param tree
     * @param filename
     * @throws IOException
     * @throws RecognitionException
     * @throws DafnyException
     */
    private void parseFile(boolean inLib, DafnyTree tree, String filename)
                    throws IOException, DafnyParserException, DafnyException {

        DafnyFileBuilder dfb = new DafnyFileBuilder();
        dfb.setInLibrary(inLib);
        dfb.setFilename(filename);
        dfb.parseRepresentation(tree);
        DafnyFile dfi = dfb.build();
        files.add(dfi);
        methods.addAll(dfi.getMethods());
        classes.addAll(dfi.getClasses());
        functions.addAll(dfi.getFunctions());
    }



    public List<DafnyFile> getFiles() {
        return files;
    }

    public List<DafnyMethod> getMethods() {
        return methods;
    }

    public List<DafnyFunction> getFunctions() {
        return functions;
    }

    public List<DafnyClass> getClasses() {
        return classes;
    }

}
