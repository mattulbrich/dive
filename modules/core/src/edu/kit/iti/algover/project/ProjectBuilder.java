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
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.SyntacticSugarVistor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FormatException;
import org.antlr.runtime.RecognitionException;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Class for building a {@link Project} object in AlgoVer.
 *
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 *
 * @author S.Grebing
 * @author M. Ulbrich
 */

public class ProjectBuilder {

    /**
     * The default filename for configuration xml documents.
     */
    public static final String CONFIG_DEFAULT_FILENAME = "config.xml";

    /**
     * List of Dafnyfiles that serve as library files (i.e., no {@link PVC} is
     * generated for them)
     */
    private final List<String> libraryFiles = new ArrayList<>();

    /**
     * All Dafny files in the project directory for which {@link PVC}s are
     * gnerated.
     */
    private final List<String> dafnyFiles = new ArrayList<>();

    /**
     * Dafny resources for which no file is present.
     *
     * This is interesting, e.g., for creating projects in testing.
     */
    private final Map<String, DafnyTree> dafnyTrees = new HashMap<>();

    /**
     * The project's directory location
     */
    private File dir;

    /**
     * The name of the file containing the configuration.
     */
    private String configFilename = CONFIG_DEFAULT_FILENAME;

    /**
     * Setting of project
     */
    private ProjectSettings settings = new ProjectSettings();

    /**
     * All processed files (to be accessed by {@link Project}'s constructor)
     */
    private List<DafnyFile> files;

    /**
     * All processed toplevel methods (to be accessed by {@link Project}'s constructor)
     */
    private List<DafnyMethod> methods;

    /**
     * All processed toplevel functions (to be accessed by {@link Project}'s constructor)
     */
    private List<DafnyFunction> functions;

    /**
     * All processed classes (to be accessed by {@link Project}'s constructor)
     */
    private List<DafnyClass> classes;

    /**
     * For some tests, name resolution must be disabled.
     */
    private boolean disableNameResolution;

    public String getConfigFilename() {
        return configFilename;
    }

    public ProjectBuilder setConfigFilename(String configFilename) {
        this.configFilename = configFilename;
        return this;
    }

    public ProjectSettings getSettings() {
        return settings;
    }

    public ProjectBuilder setSettings(ProjectSettings settings) {
        this.settings = settings;
        return this;
    }

    public ProjectBuilder setSettings(Map<String, String> settings) {
        this.settings = new ProjectSettings(settings);
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
     * This method loads the configuration file, extracts all entities and sets member variables accordingly
     */
    public void parseProjectConfigurationFile() throws IOException, JAXBException, SAXException {

        File configFile = new File(getDir() + File.separator + getConfigFilename());

        Configuration config = ConfigXMLLoader.loadConfigFile(configFile);

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

        Map<String, String> settings = config.getSettings();
        if(settings != null) {
            this.setSettings(settings);
        }
    }

    /**
     * Ensures that the information in the config file was valid.
     *
     * <p>In particular: Settings are valid and files exist.
     *
     * @throws IOException if file(s) do not exist
     * @throws FormatException if settings are illegal
     */
    public void validateProjectConfiguration() throws IOException, FormatException {
        this.getSettings().validate();

        for(String f : this.getLibraryFiles()) {
            if(!new File(dir, f).exists()) {
                throw new FileNotFoundException(f);
            }
        }

        for(String f : this.getDafnyFiles()) {
            if(!new File(dir, f).exists()) {
                throw new FileNotFoundException(f);
            }
        }
    }

    /**
     * Builds {@link Project} object from the resources set here..
     *
     * @return a freshly created {@link Project} object.
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     * @throws DafnyParserException
     *             if the dafny parser complains with a syntax error
     * @throws DafnyException
     *             if analysis of the dafny tree fails (name resolution, typing,
     *             ...)
     */
    public Project build() throws IOException, DafnyException, DafnyParserException {
        this.files = new ArrayList<>();
        this.methods = new ArrayList<>();
        this.functions = new ArrayList<>();
        this.classes = new ArrayList<>();

        // parse DafnyFiles: first libs, then sources
        for (String file: this.getLibraryFiles()) {
            DafnyTree tree = DafnyFileParser.parse(new File(dir, file));
            parseFile(true, tree, file);
        }

        for (String file: this.getDafnyFiles()) {
            DafnyTree tree = DafnyFileParser.parse(new File(dir, file));
            parseFile(false, tree, file);
        }

        for (Map.Entry<String, DafnyTree> en : dafnyTrees.entrySet()) {
            parseFile(true, en.getValue(), en.getKey());
        }

        Project project = new Project(this);
        SyntacticSugarVistor.visitProject(project);
        resolveNames(project);

        //TODO parse rules for project

        return project;
    }


    /*
     * Prepare the DafnyTrees by applying relevant visitors for name resolution
     * etc.
     */
    private void resolveNames(Project p) throws DafnyException {

        // for some test cases, name resolution must be switched off
        if (disableNameResolution) {
            return;
        }

        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor refResolver = new ReferenceResolutionVisitor(p, exceptions);
        refResolver.visitProject();

        // TODO make the other exceptions accessible as well;
        if (!exceptions.isEmpty()) {
            throw exceptions.get(0);
        }

        TypeResolution typeRes = new TypeResolution(exceptions);
        typeRes.visitProject(p);

        if (!exceptions.isEmpty()) {
            throw exceptions.get(0);
        }
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
     * Access function for the constructor of {@link Project}.
     * @return all processed dafny files
     */
    List<DafnyFile> getFiles() {
        return files;
    }

    /**
     * Access function for the constructor of {@link Project}.
     * @return all processed dafny methods
     */
    List<DafnyMethod> getMethods() {
        return methods;
    }

    /**
     * Access function for the constructor of {@link Project}.
     * @return all processed dafny functions
     */
    List<DafnyFunction> getFunctions() {
        return functions;
    }

    /**
     * Access function for the constructor of {@link Project}.
     * @return all processed dafny classes
     */
    List<DafnyClass> getClasses() {
        return classes;
    }

    /**
     * For testing!
     */
    public void disableNameResolution() {
        this.disableNameResolution = true;
    }

}
