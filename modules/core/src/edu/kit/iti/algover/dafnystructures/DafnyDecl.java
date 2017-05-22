/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * Created by sarah on 8/4/16.
 */
public abstract class DafnyDecl {

    /**
     * File, in which this DafnyDecl is stored in
     */
    private final String filename;

    /**
     * Reference to ASTs that represents this DafnyDecl
     */
    private final DafnyTree representation;

    private final String name;

    private final boolean inLibrary;

    public DafnyDecl(String filename, DafnyTree tree, String name, boolean inLib){
        this.representation = tree;
        this.filename = filename;
        this.name = name;
        this.inLibrary = inLib;
    }

    // REVIEW: What is a representation? Is this the AST source of this decl?
    public DafnyTree getRepresentation() {
        return representation;
    }

    public String getFilename() {
        return filename;
    }

    public String getName() {
        return name;
    }

    public boolean isInLibrary() {
        return inLibrary;
    }

    public abstract <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg);

    public static <D extends DafnyDecl> Map<String, D> toMap(List<D> list) throws DafnyException {
        Map<String, D> result = new LinkedHashMap<String, D>();
        for (D decl : list) {
            if(result.containsKey(decl.getName())) {
                throw new DafnyException("XXX", decl.getRepresentation());
            }
            result.put(decl.getName(), decl);
        }
        return result;
    }

}
