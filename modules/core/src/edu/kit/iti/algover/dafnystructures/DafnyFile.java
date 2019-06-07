/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyException;

import java.util.Collection;
import java.util.Map;

/**
 * A file containting dafny declarations.
 * @author Sarah Grebing
 * @author Mattias Ulbrich
 */
public class DafnyFile extends DafnyDecl {

    /**
     * Methods belonging to this file, possibly empty.
     * Indexed by their name.
     */
    private Map<String, DafnyMethod> methods;

    /**
     * Functions belonging to this class, possibly empty.
     * Indexed by their name.
     */
    private Map<String, DafnyFunction> functions;

    /**
     * Classes belonging to this class, possibly empty.
     * Indexed by their name.
     */
    private Map<String, DafnyClass> classes;

    /**
     * Instantiates a new dafny file from a builder.
     *
     * @param b the builder from which data is to be taken, not <code>null</code>
     * @throws DafnyException if name conflicts arise.
     */
    public DafnyFile(DafnyFileBuilder b) throws DafnyException {
        super(b.getFilename(), b.getRepresentation(), b.getFilename(), b.isInLibrary());
        this.methods = toMap(b.getMethods());
        this.classes = toMap(b.getClasses());
        this.functions = toMap(b.getFunctions());

        checkNameConflict(b.getMethods(), b.getFunctions());

        setParentFor(methods.values());
        setParentFor(functions.values());
        setParentFor(classes.values());
    }

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    public Collection<DafnyMethod> getMethods() {
        return methods.values();
    }

    public Collection<DafnyFunction> getFunctions() {
        return functions.values();
    }

    public Collection<DafnyClass> getClasses() {
        return classes.values();
    }

}