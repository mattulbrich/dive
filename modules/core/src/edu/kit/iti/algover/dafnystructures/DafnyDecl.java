/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;

/**
 * Base class for all Dafny declarations.
 */
public abstract class DafnyDecl {

    /**
     * Filename of the file in which this DafnyDecl is stored.
     */
    private final String filename;

    /**
     * Reference to the AST that represents this declaration.
     */
    private final DafnyTree representation;

    /**
     * The name of this declaration.
     */
    private final String name;

    /**
     * a flag indicating whether this declaration is a library entity or not.
     *
     * Invariant: All children elements of declaration must have the same value
     * for the library flag.
     */
    private final boolean inLibrary;

    /**
     * Instantiates a new dafny declaration.
     *
     * @param filename
     *            the filename
     * @param tree
     *            the AST to which this declaration points
     * @param name
     *            the name of the entity.
     * @param inLib
     *            <code>true</code> iff this is a library entity
     */
    public DafnyDecl(String filename, DafnyTree tree, String name, boolean inLib) {
        this.representation = Objects.requireNonNull(tree);
        this.filename = Objects.requireNonNull(filename);
        this.name = Objects.requireNonNull(name);
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

    /**
     * Checks if this entitiy is a library entity.
     *
     * @return true iff is marked as library
     */
    public boolean isInLibrary() {
        return inLibrary;
    }

    /**
     * Accept a visitor for declarations.
     *
     * This is part of a visitor pattern.
     *
     * @param <R>
     *            the result type of the visitor
     * @param <A>
     *            the argument type of the visitor
     * @param visitor
     *            actual the visitor
     * @param arg
     *            the argument to be passed to the visitor
     * @return the result returned by the visitor
     */
    public abstract <R, A> R accept(DafnyDeclVisitor<R, A> visitor, A arg);

    /**
     * Check two maps of declarations for a name conflict.
     *
     * @param list1
     *            one collections of declarations, indexed by name, not
     *            <code>null</code>
     * @param list2
     *            another collections of declarations, indexed by name, not
     *            <code>null</code>
     * @throws DafnyException
     *             if two declarations by the same exist
     */
    protected static void checkNameConflict(Map<String, ? extends DafnyDecl> list1,
            Map<String, ? extends DafnyDecl> list2) throws DafnyException {
        Set<String> knownNames = new HashSet<>(list1.keySet());
        knownNames.retainAll(list2.keySet());

        if (!knownNames.isEmpty()) {
            String name = knownNames.iterator().next();
            DafnyDecl instance = list2.get(knownNames);
            throw new DafnyException("Function/method " + name + " has been declared twice.",
                    instance.getRepresentation());
        }
    }

    /**
     * Translate a list of dafny declarations to a map by their name.
     *
     * @param <D>
     *            the generic type
     * @param list
     *            the list
     * @return the map
     * @throws DafnyException
     *             the dafny exception
     */
    public static <D extends DafnyDecl> Map<String, D> toMap(List<D> list) throws DafnyException {
        Map<String, D> result = new LinkedHashMap<String, D>();
        for (D decl : list) {
            if (result.containsKey(decl.getName())) {
                // TODO bring up a sensible error message
                throw new DafnyException("XXX", decl.getRepresentation());
            }
            result.put(decl.getName(), decl);
        }
        return result;
    }

    public Collection<FunctionSymbol> getLocalSymbols() {
        return Collections.emptyList();
    }

}
