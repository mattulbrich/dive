/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import java.io.File;
import java.util.*;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyDeclPVCCollector;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.term.FunctionSymbol;
import nonnull.NonNull;


// REVIEW: I miss a possibility to retrieve all parsed DafnyTrees (toplevel entities)
// How can one obtain these?

// SaG: by getting all PVCCollections from Map pvc and rertieving tree by
// PVCCollection.getDafnyDecl().getRepresentation()



/**
 * Class representing a project, that contains all relevant information for a
 * project that should be verified
 *
 * @author Created by sarah on 8/3/16.
 * @author revised by mattias
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

    /**
     * Lookup maps to get Dafny classes of the project-
     */
    private final Map<String, DafnyClass> classes;

    /**
     * Lookup maps to get Dafny toplevel methods of the project-
     */
    private final Map<String, DafnyMethod> methods;

    /**
     * Lookup maps to get Dafny toplevel functions of the project-
     */
    private final Map<String, DafnyFunction> functions;

    /**
     * Lookup maps to get the {@link FunctionSymbol}s corresponding
     * to the functions and fields of the project.
     * <p>
     * Lazily created.
     */
    private Collection<FunctionSymbol> functionSymbols;

    /**
     * The tree data structure for all {@link PVC}s.
     * <p>
     * Lazily created.
     */
    private PVCGroup pvcRoot;

    /**
     * A map from identifier to {@link PVC}.
     *
     * Lazily created.
     */
    private Map<String, PVC> pvcByName;

    /**
     * A collection of all proof rules available in this project
     */
    private Collection<ProofRule> allProofRules;


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
        this.pvcByName = new HashMap<>();
        this.allProofRules = new ArrayList<>();
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

    public Collection<ProofRule> getAllProofRules() {
        return allProofRules;
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

    @Override
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

    /**
     * Return all PVCs of the project.
     *
     * @return the PVCs as tree data structure.
     */
    public @NonNull PVCGroup getAllPVCs() {
        ensurePVCsExist();
        return pvcRoot;
    }

    /**
     * Generates the PVCs for this project. Saves the PVCs to the String lookup
     * map.
     * <p>
     * This is not thread-safe, but can be made so easily.
     */
    private PVCGroup ensurePVCsExist() {

        if (pvcRoot != null) {
            return pvcRoot;
        }

        PVCGroup root = new PVCGroup(null);

        DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(this);
        for (DafnyFile file : this.getDafnyFiles()) {
            visitor.visitFile(file, root);
        }

        pvcByName = new HashMap<>();
        for (PVC pvc : root.getContents()) {
            pvcByName.put(pvc.getIdentifier(), pvc);
        }

        this.pvcRoot = root;
        return root;

    }

    /**
     * Gets a map from identifiers to project PVCs.
     *
     * @return an unmodifiable map.
     */
    public @NonNull Map<String, PVC> getPVCByNameMap() {
        ensurePVCsExist();
        return Collections.unmodifiableMap(pvcByName);
    }

    /**
     * Get the PVCs for a DafnyDecl as tree.
     *
     * @param decl the declaration to look up
     * @return the corresponding PVC collection
     * @throws NoSuchElementException if the declaration is not known
     */
    public PVCCollection getPVCsFor(DafnyDecl decl) {
        ensurePVCsExist();
        for (PVCCollection child : pvcRoot.getChildren()) {
            if (child.getDafnyDecl() == decl) {
                return child;
            }
        }

        throw new NoSuchElementException();
    }

    /**
     * Gets a PVC by identifier.
     *
     * @param name
     *            the identifier to look up
     * @return the created PVC with the name, or <code>null</code> if that
     *         identifier has no PVC assigned to it.
     */
    public PVC getPVCByName(String name) {
        ensurePVCsExist();
        return pvcByName.get(name);
    }

    /**
     * Gets the all declared functions symbols.
     * <p>
     * These are triggered by field and function declarations.
     *
     * @return the unmodifiable collection of all declared symbols
     */
    public Collection<FunctionSymbol> getAllDeclaredSymbols() {
        if (functionSymbols == null) {
            functionSymbols = DeclarationSymbolCollector.collect(this);
        }

        return Collections.unmodifiableCollection(functionSymbols);
    }


    /**
     * This method extracts the proof rules from and saves them to this object
     */
    public void extractProofRules() {
        throw new Error("to be done");
    }
}
