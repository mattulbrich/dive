/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
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
import nonnull.NonNull;
import org.antlr.runtime.RecognitionException;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
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
     * The project's base directory directory.
     *
     * All file names are resolved wrt to this directory.
     */
    private File dir;

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
        return Collections.unmodifiableList(libraryFiles);
    }

    public void addLibraryFile(String file) {
        libraryFiles.add(file);
    }

    public List<String> getDafnyFiles() {
        return Collections.unmodifiableList(dafnyFiles);
    }

    /**
     * Add a filename to the files to be parsed. The filename is interpreted
     * relative to the value of {@link #dir}.
     *
     * @param file filename of a .dfy file to be read
     */
    public void addInputFile(@NonNull String file) {
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
            if(f.startsWith("$dive/")) {
                URL url = getClass().getResource("lib/" + f.substring(6));
                if (url == null) {
                    throw new FileNotFoundException("Internal library not found: " + f);
                }
            } else {
                // MU: bugfix to deal with absolute paths
                File file = getFileFor(f);
                if (!file.exists()) {
                    throw new FileNotFoundException(file.toString());
                }
            }
        }

        for(String f : this.getDafnyFiles()) {
            File file = getFileFor(f);
            if(!file.exists()) {
                throw new FileNotFoundException(file.toString());
            }
        }
    }

    /**
     * get a File object for the file name string. If the string is an absolute
     * file name, return that. Otherwise make it relative to the directory.
     */
    private File getFileFor(String f) {
        File result = new File(f);
        if (result.isAbsolute()) {
            return result;
        }
        return new File(dir, f);
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
        for (String filename: this.getLibraryFiles()) {
            // TODO ... and Windows users?
            DafnyTree tree;
            if(filename.startsWith("$dive/")) {
                URL url = getClass().getResource("lib/" + filename.substring(6));
                if (url == null) {
                    throw new FileNotFoundException("Internal library not found: " + filename);
                }
                tree = DafnyFileParser.parse(url.openStream());
                tree.setFilename(filename);
            } else {
                File file = getFileFor(filename);
                tree = DafnyFileParser.parse(file);
            }
            parseFile(true, tree, filename);
        }

        for (String filename: this.getDafnyFiles()) {
            File file = getFileFor(filename);
            DafnyTree tree = DafnyFileParser.parse(file);
            parseFile(false, tree, filename);
        }

        // That's used in testing ...
        for (Map.Entry<String, DafnyTree> en : dafnyTrees.entrySet()) {
            parseFile(false, en.getValue(), en.getKey());
        }

        Project project = new Project(this);
        SyntacticSugarVistor.visitProject(project);
        resolveNames(project);
        TarjansAlgorithm tarjan = new TarjansAlgorithm(project);
        tarjan.computeSCCs();

        return project;
    }

    public static Project emptyProject(File baseDir) {
        ProjectBuilder pb = new ProjectBuilder();

        pb.setDir(baseDir);
        pb.files = Collections.emptyList();
        pb.methods = Collections.emptyList();
        pb.functions = Collections.emptyList();
        pb.classes = Collections.emptyList();

        try {
            return new Project(pb);
        } catch (DafnyException e) {
            // This is unreachable due to the structure of the empty project.
            throw new Error("Unreachable!", e);
        }

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
