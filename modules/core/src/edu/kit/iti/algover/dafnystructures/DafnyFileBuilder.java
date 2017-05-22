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

public class DafnyFileBuilder {

    private String filename;
    private DafnyTree representation;
    private boolean inLibrary;
    private List<DafnyMethod> methods = new ArrayList<>();
    private List<DafnyFunction> functions = new ArrayList<>();
    private List<DafnyClass> classes = new ArrayList<>();

    public DafnyFileBuilder() {
    }

    public void parseRepresentation(DafnyTree tree) throws DafnyException {
        assert this.representation == null :
            "A builder must not have its representation replaced";

        this.representation = tree;

        for (DafnyTree child : tree.getChildren()) {
            switch(child.getType()) {
            case DafnyParser.METHOD:
                DafnyMethodBuilder methBuilder = new DafnyMethodBuilder(filename);
                methBuilder.setInLibrary(inLibrary);
                methBuilder.parseRepresentation(child);
                methods.add(methBuilder.build());
                break;
            case DafnyParser.FUNCTION:
                DafnyFunctionBuilder fctBuilder = new DafnyFunctionBuilder(filename);
                fctBuilder.parseRepresentation(child);
                fctBuilder.setInLibrary(inLibrary);
                functions.add(fctBuilder.build());
                break;
            case DafnyParser.CLASS:
                DafnyClassBuilder classBuilder = new DafnyClassBuilder(filename);
                classBuilder.setInLibrary(inLibrary);
                classBuilder.parseRepresentation(child);
                classes.add(classBuilder.build());
                break;
            default:
                throw new Error("unreachable");
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

    public DafnyFile build() throws DafnyException {
        return new DafnyFile(this);
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