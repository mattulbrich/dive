/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFileBuilder;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.script.ScriptFileParser;
import edu.kit.iti.algover.script.ScriptParser;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FileUtil;

/**
 * Class for building a project in AlgoVer
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 * Created by sarah on 8/3/16.
 */
// REVIEW: Add Javadoc
public class ProjectBuilder {

    /**
     * The project's directory location
     */
    private File dir;

    private final List<String> libraryFiles = new ArrayList<>();

    /**
     * All Dafnyfiles in the project directory
     */
    private final List<String> dafnyFiles = new ArrayList<>();

    /**
     * The script of the project
     */
    // TODO make constant for string
    // REVIEW: Should it really be called ".script"?
    private String scriptFilename = "project.script";

    /**
     * Setting of project
     */
    private ProjectSettings settings = new ProjectSettings();

    private List<DafnyFile> files;

    private List<DafnyMethod> methods;

    private List<DafnyFunction> functions;

    private List<DafnyClass> classes;

    private final Map<String, DafnyTree> dafnyTrees = new HashMap<>();

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

    // REVIEW: Is it still a script? More a "project" file by now.
    public void parseScript() throws IOException, RecognitionException {
        ScriptTree parsedScript = parseScriptFile(getScriptFilename());

        // extract settings from ScriptTree and change settings in data structure
        extractSettings(parsedScript.getFirstChildWithType(ScriptParser.SETTINGS));

        // extract dafnyfiles into datastructure
        extractDafnyFileNames(parsedScript.getFirstChildWithType(ScriptParser.IMPORT));

        // extract Dafnylib files into datastructure
        extractDafnyFileNames(parsedScript.getFirstChildWithType(ScriptParser.LIBRARY));
    }

    public Project build() throws IOException, DafnyParserException, DafnyException {
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

    /**
     * Extract DafnyFilenames from a subtree that has import as root and create
     * new File with current Directory
     */
    private void extractDafnyFileNames(ScriptTree t) {
        int type = t.getType();
        List<ScriptTree> dafnyF = t.getChildrenWithType(ScriptParser.FILE);

        for (ScriptTree tree : dafnyF) {
            // REVIEW This does not work work longer filenames ...
            // FIXME!
            File f = new File(tree.getChild(0).getText() + tree.getChild(1).getText());
            switch (type) {
            case ScriptParser.IMPORT:
                this.addDafnyFile(f.toString());
                break;
            case ScriptParser.LIBRARY:
                this.addLibraryFile(f.toString());
                break;
            default:
                throw new Error("unexpected type " + type);
            }
        }
    }

    /**
     * Parse Script File and return Tree to traverse
     *
     * @param relativeFilename
     * @return
     * @throws IOException
     * @throws RecognitionException
     */
    private ScriptTree parseScriptFile(String relativeFilename) throws IOException, RecognitionException {
        try(InputStream scriptStream = FileUtil.readFile(new File(dir, relativeFilename))) {
            return ScriptFileParser.parse(scriptStream);
        }
    }

    /**
     * Extract Settings and add them to settingsobject (maybe refactor to
     * settings class)
     *
     * @param t
     *            ScriptTree with root node Settings
     */
    private void extractSettings(ScriptTree t){
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
