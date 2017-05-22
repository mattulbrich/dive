/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.Collection;
import java.util.Map;

import edu.kit.iti.algover.parser.DafnyException;

public class DafnyFile extends DafnyDecl {

    /**
     * Methods belonging to this class, possibly empty
     */
    private Map<String, DafnyMethod> methods;

    /**
     * Functions belonging to this class, possibly empty
     */
    private Map<String, DafnyFunction> functions;


    private Map<String, DafnyClass> classes;

    public DafnyFile(DafnyFileBuilder b) throws DafnyException {
        super(b.getFilename(), b.getRepresentation(), b.getFilename(), b.isInLibrary());
        this.methods = toMap(b.getMethods());
        this.classes = toMap(b.getClasses());
        this.functions = toMap(b.getFunctions());
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