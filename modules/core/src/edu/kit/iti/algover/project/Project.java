/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import java.io.File;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.settings.ProjectSettings;


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

    /**
     * Constructor can only be called using a ProjectBuilder
     * @param pBuilder
     * @throws DafnyException
     */
    public Project(ProjectBuilder pBuilder) throws DafnyException{
        this.settings = pBuilder.getSettings();
        this.dafnyFiles = pBuilder.getFiles();
        this.classes = DafnyDecl.toMap(pBuilder.getClasses());
        this.functions = DafnyDecl.toMap(pBuilder.getFunctions());
        this.methods = DafnyDecl.toMap(pBuilder.getMethods());
        this.baseDir = pBuilder.getDir();
    }

    public String toString(){
        // REVIEW should use StringBuilder
        String s = "Project\n";
        if(classes.size() != 0) {
            s += "with ";
            s += this.classes.size();
            s += " classe(s): \n";
            for (DafnyClass dClass : this.getClasses()) {
                s += dClass.toString();
            }
        }else{
            s += "with ";
            s += this.methods.size();
            s += " method(s): \n";
            for (DafnyMethod m : this.getMethods()) {

                s += m.toString();
            }
        }
        return s;

    }

    public List<PVC> getAllVerificationConditions() {
        throw new UnsupportedOperationException();
    }

    public List<PVC> getVerificationConditionsFor(DafnyDecl decl) {
        throw new UnsupportedOperationException();
    }

}
