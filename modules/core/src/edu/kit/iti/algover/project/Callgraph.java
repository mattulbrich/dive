/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyTree;
import nonnull.NonNull;

import java.util.Collection;
import java.util.NoSuchElementException;

/**
 * This class implements a simple call graph for Dafny projects on method
 * level.
 *
 * The structure allows to query all calls that relate to a Dafny method {@code
 * method}.
 *
 * Using {@link #getCalls(DafnyDecl)} all <em>outgoing</em> method
 * calls, i.e. all Dafny AST nodes that implement a call to some (other) method
 * from within {@code method} can be obtained.
 *
 * Using {@link #getCallsites(DafnyDecl)} all <em>incoming</em> method
 * calls, i.e. all Dafny AST nodes that implement a call to {@code  method} can
 * be obtained.
 *
 * Method {@link #getMethod(DafnyTree)} can be used to resolve the method object
 * from the AST node obtained by the other methods.
 *
 * @author Mattias Ulbrich
 */
public class Callgraph {

    private final @NonNull Project project;

    /**
     * create a new call graph for the methods of the argument
     *
     * @param project any project.
     */
    public Callgraph(@NonNull Project project) {
        this.project = project;
        initialize();
    }

    private void initialize() {
    }

    /**
     * Obtain all <em>incoming</em> calls, i.e. all Dafny AST nodes that
     * implement a call to {@code  callableDecl}.
     *
     * The result is a collection of {@link DafnyTree}s such that the following
     * is true for any {@code x} of them:
     * <ul>
     * <li>ID is {@link edu.kit.iti.algover.parser.DafnyParser#CALL} and</li>
     * <li>{@code x.getDeclarationReference() == callableDecl.getRepresentation()}</li>
     * </ul>
     *
     * @param callableDecl a callableDecl or function within the project of this
     *                     call graph
     * @return an unmodifiable collection of callsites
     */
    public Collection<DafnyTree> getCallsites(DafnyDecl callableDecl) {
        throw new UnsupportedOperationException("not yet implemented");
    }

    /**
     * Obtain all <em>outgoing</em> callableDecl calls, all Dafny AST nodes that
     * implement a call to some (other) callableDecl from within {@code
     * callableDecl}.
     *
     * The result is a collection of {@link DafnyTree}s such that the following
     * is true for any {@code x} of them:
     * <ul>
     * <li>ID is {@link edu.kit.iti.algover.parser.DafnyParser#CALL} and</li>
     * <li>{@code callableDecl.getRepresentation()} is an AST parent of {@code
     * x}</li>
     * </ul>
     *
     * @param callableDecl a callableDecl within the project of this call graph
     * @return an unmodifiable collection of callsites
     */
    public Collection<DafnyTree> getCalls(DafnyDecl callableDecl) {
        throw new UnsupportedOperationException("not yet implemented");
    }

    /**
     * Obtain the declaration that belongs to a particular call.
     *
     * It works for all {@link DafnyTree}s obtained from {@link
     * #getCalls(DafnyDecl)} and {@link #getCallsites(DafnyDecl)}.
     *
     * @param tree an AST representing a call
     * @return the corresponding dafny declaration within the project
     * @throws NoSuchElementException if tree does not correspond to a call to
     *                                an entitity within the project.
     */
    public static DafnyDecl getMethod(DafnyTree tree) throws NoSuchElementException {
        throw new UnsupportedOperationException("not yet implemented");
    }

}
