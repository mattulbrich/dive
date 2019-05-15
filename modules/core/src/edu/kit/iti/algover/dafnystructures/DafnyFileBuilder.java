/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * The builder for {@link DafnyFile}s.
 *
 * The constructor of {@link DafnyFile}s takes an object of this class as
 * argument.
 *
 * @see DafnyFile
 */
public class DafnyFileBuilder {

    /**
     * The filename of the file
     */
    private String filename;

    /**
     * The AST base
     */
    private DafnyTree representation;

    /**
     * The flag whether or not this is a library.
     */
    private boolean inLibrary;

    /**
     * The collection of methods, not <code>null</code>, but possibly empty.
     */
    private List<DafnyMethod> methods = new ArrayList<>();

    /**
     * The collection of functions, not <code>null</code>, but possibly empty.
     */
    private List<DafnyFunction> functions = new ArrayList<>();

    /**
     * The collection of classes, not <code>null</code>, but possibly empty.
     */
    private List<DafnyClass> classes = new ArrayList<>();

    /**
     * Instantiates a new dafny file builder.
     *
     * All fields are set to <code>null</code>, the lists are initialised to
     * empty sets.
     */
    public DafnyFileBuilder() {
    }

    /**
     * Parses the AST.
     *
     * The AST must not have been set prior to this call.
     *
     * @param tree
     *            the tree, not <code>null</code>
     * @throws DafnyException
     *             if conflicting entities are around.
     */
    public void parseRepresentation(DafnyTree tree) throws DafnyException {
        assert this.representation == null
                : "A builder must not have its representation replaced";

        this.representation = tree;

        for (DafnyTree child : tree.getChildren()) {
            switch (child.getType()) {
            case DafnyParser.METHOD:
                DafnyMethodBuilder methBuilder = new DafnyMethodBuilder(filename);
                methBuilder.setInLibrary(inLibrary);
                methBuilder.parseRepresentation(child);
                methods.add(methBuilder.build());
                break;
            case DafnyParser.FUNCTION:
                DafnyFunctionBuilder fctBuilder = new DafnyFunctionBuilder();
                fctBuilder.setFilename(filename);
                fctBuilder.setInLibrary(inLibrary);
                fctBuilder.parseRepresentation(child);
                functions.add(fctBuilder.build());
                break;
            case DafnyParser.CLASS:
                DafnyClassBuilder classBuilder = new DafnyClassBuilder();
                classBuilder.setFilename(filename);
                classBuilder.setInLibrary(inLibrary);
                classBuilder.parseRepresentation(child);
                classes.add(classBuilder.build());
                break;
            case DafnyParser.INCLUDE:
            case DafnyParser.SUBSUME:
            case DafnyParser.SETTINGS:
                // Ignore the configuration stuff when parsing files.
                break;
            default:
                System.err.println(child.toStringTree());
                throw new Error("unexpected toplevel AST element of type " + child.getType());
            }
        }
    }

    public String getFilename() {
        return filename;
    }

    public void setFilename(String filename) {
        this.filename = filename;
    }

    public DafnyTree getRepresentation() {
        return representation;
    }

    public boolean isInLibrary() {
        return inLibrary;
    }

    public void setInLibrary(boolean inLibrary) {
        this.inLibrary = inLibrary;
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

    /**
     * Create a dafny file fromt the information here
     *
     * @return the freshly created dafny file
     * @throws DafnyException
     *             if conflictingly named entities exist
     */
    public DafnyFile build() throws DafnyException {
        return new DafnyFile(this);
    }
}