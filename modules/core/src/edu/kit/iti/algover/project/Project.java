/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.term.FunctionSymbol;

import java.io.File;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;


// REVIEW: I miss a possibility to retrieve all parsed DafnyTrees (toplevel entities)
// How can one obtain these?

// REVIEW: Would it make sense to habe a lookup table indexed by name?

/**
 * Class representing a project, that contains all relevant information for a
 * project that should be verified Created by sarah on 8/3/16.
 */
public class Project {

    /**
     * The base directory under which all files must be located.
     */
    private final File baseDir;

    /**
     * List containing references to all problem files
     * All imported libraries
     */
    private final List<DafnyFile> dafnyFiles;

    /**
     * Settings of Project
     */
    private final ProjectSettings settings;

    private Map<String, DafnyClass> classes;

    private Map<String, DafnyMethod> methods;

    private Map<String, DafnyFunction> functions;

    private Collection<FunctionSymbol> functionSymbols;

    /**
     * Constructor can only be called using a ProjectBuilder
     *
     * @param pBuilder
     * @throws DafnyException
     */
    public Project(ProjectBuilder pBuilder) throws DafnyException {
        this.settings = pBuilder.getSettings();
        this.dafnyFiles = pBuilder.getFiles();
        this.classes = DafnyDecl.toMap(pBuilder.getClasses());
        this.functions = DafnyDecl.toMap(pBuilder.getFunctions());
        this.methods = DafnyDecl.toMap(pBuilder.getMethods());
        this.baseDir = pBuilder.getDir();
    }

    public File getBaseDir() {
        return baseDir;
    }

    public Collection<DafnyFunction> getFunctions() {
        return functions.values();
    }

    public DafnyFunction getFunction(String name) {
        return functions.get(name);
    }

    public Collection<DafnyMethod> getMethods() {
        return methods.values();
    }

    public DafnyMethod getMethod(String name) {
        return methods.get(name);
    }

    public Collection<DafnyClass> getClasses() {
        return classes.values();
    }

    /**
     * Gets a class from this project by name.
     *
     * @param classname
     *            the non-<code>null</code> classname
     * @return the class named <tt>classname</tt>, or <code>null</code> if not
     *         existing
     */
    public DafnyClass getClass(String classname) {
        return classes.get(classname);
    }

    public List<DafnyFile> getDafnyFiles() {
        return dafnyFiles;
    }

    public ProjectSettings getSettings() {
        return settings;
    }

    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append("Project\n");
        if(classes.size() != 0) {
            s.append("with " + this.classes.size() + " classe(s): \n");
            for (DafnyClass dClass : this.getClasses()) {
                s.append(dClass.toString());
            }
        } else {
            s.append("with " + this.methods.size() + " method(s): \n");
            for (DafnyMethod m : this.getMethods()) {

                s.append(m.toString());
            }
        }
        return s.toString();

    }

    public PVCGroup getAllVerificationConditions() {
        return this.generateAndCollectPVC();
    }

    public PVCGroup getVerificationConditionsFor(DafnyDecl decl) {
        throw new UnsupportedOperationException();
    }

    public Collection<FunctionSymbol> getAllDeclaredSymbols() {
        if(functionSymbols == null) {
            functionSymbols = DeclarationSymbolCollector.collect(this);
        }
        return Collections.unmodifiableCollection(functionSymbols);
    }


    /**
     * Performs Symbolic execution of a dafnydecl and return the list of PVCs
     *
     * @return the root of the PVCGroup for this project
     */

    public PVCGroup generateAndCollectPVC() {

        PVCGroup root = new PVCGroup(null);

        DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector();

        for (DafnyFile file : this.getDafnyFiles()) {
            visitor.visitFile(file, root);
        }

        return root;

    }
}
