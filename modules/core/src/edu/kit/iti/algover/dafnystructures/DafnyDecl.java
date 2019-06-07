/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;

import java.util.*;

/**
 * Base class for all Dafny declarations.
 *
 * @author Sarah Grebing
 * @author Mattias Ulbrich
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
     * The declaration within which this declaration is placed.
     * May be <code>null</code> (in particular for {@link DafnyFile}s)
     * <p>
     * This is set by the parent class when adding it as a child.
     */
    private DafnyDecl parentDecl;

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

    /**
     * Check two maps of declarations for a name conflict.
     *
     * A conflict occurs if there are two declarations that have the same name
     * in the given collection..
     *
     * @param declarations  a collections of declarations, indexed by name, not
     *                      <code>null</code>
     * @param declarations2 another collections of declarations, indexed by
     *                      name, not
     *                      <code>null</code>
     * @throws DafnyException if there is a name conflict between the
     *                        declarations in the two lists
     */
    protected static void checkNameConflict(Collection<? extends DafnyDecl> declarations,
                                            Collection<? extends DafnyDecl> declarations2) throws DafnyException {
        Set<String> seenNames = new HashSet<>();

        for (DafnyDecl decl : declarations) {
            if (seenNames.contains(decl.getName())) {
                throw new DafnyException("This scope already contains a declaration named " + decl.getName(),
                        decl.getRepresentation());
            }
            seenNames.add(decl.getName());
        }
        for (DafnyDecl decl : declarations2) {
            if (seenNames.contains(decl.getName())) {
                throw new DafnyException("This scope already contains a declaration named " + decl.getName(),
                        decl.getRepresentation());
            }
            seenNames.add(decl.getName());
        }
    }

    /**
     * Translate a list of dafny declarations to a map by their name.
     * <p>
     * This is a infrastructure method invoked by various builders.
     *
     * @param <D>  the generic type
     * @param list the list
     * @return the map
     * @throws DafnyException the dafny exception
     */
    public static <D extends DafnyDecl> Map<String, D> toMap(List<D> list) throws DafnyException {
        Map<String, D> result = new LinkedHashMap<String, D>();
        for (D decl : list) {
            result.put(decl.getName(), decl);
        }
        return result;
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

    public DafnyDecl getParentDecl() {
        return parentDecl;
    }

    /**
     * Sets the {@link #parentDecl} field of the argument declarations to this
     * object.
     *
     * @param decls
     *            collection of the declarations in which the parent is to be
     *            set
     */
    void setParentFor(Collection<? extends DafnyDecl> decls) {
        for (DafnyDecl decl : decls) {
            assert decl.parentDecl == null;
            decl.parentDecl = this;
        }
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
     * Checks if this entity is declared within a class.
     *
     * @return true iff it is the member of a class.
     */
    public boolean isDeclaredInClass() {
        return getParentDecl() instanceof DafnyClass;
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

    public Collection<FunctionSymbol> getLocalSymbols() {
        return Collections.emptyList();
    }

}
