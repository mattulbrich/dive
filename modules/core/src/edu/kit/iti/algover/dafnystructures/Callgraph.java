/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import edu.kit.iti.algover.project.Project;
import nonnull.NonNull;
import org.antlr.runtime.tree.Tree;

import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
 * Method {@link #getDecl(DafnyTree)} can be used to resolve the method object
 * from the AST node obtained by the other methods.
 *
 * @author Mattias Ulbrich
 */
public class Callgraph {

    private final @NonNull Project project;

    private final Map<DafnyDecl, List<DafnyTree>> callMap =
            new IdentityHashMap<>();

    private final Map<DafnyDecl, List<DafnyTree>> callSiteMap =
            new IdentityHashMap<>();

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
        project.getMethods().forEach(this::iterateCallable);
        project.getFunctions().forEach(this::iterateCallable);
        for (DafnyClass clss : project.getClasses()) {
            clss.getMethods().forEach(this::iterateCallable);
            clss.getFunctions().forEach(this::iterateCallable);
        }
    }

    private void iterateCallable(DafnyDecl decl) {
        decl.getRepresentation().accept(new Visitor(), decl);
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
        return Collections.unmodifiableList(
                callSiteMap.getOrDefault(callableDecl, Collections.emptyList()));
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
        return Collections.unmodifiableList(
                callMap.getOrDefault(callableDecl, Collections.emptyList()));
    }

    /**
     * Obtain the declaration that belongs to a particular call.
     *
     * It works for all {@link DafnyTree}s obtained from {@link
     * #getCalls(DafnyDecl)} and {@link #getCallsites(DafnyDecl)}.
     *
     * @param tree an AST representing a call
     * @return the corresponding dafny declaration within the project
     */
    public DafnyDecl getDecl(DafnyTree tree) {

        assert tree.getType() == DafnyParser.CALL;

        DafnyTree declRef = tree.getChild(0).getDeclarationReference();
        int ty = declRef.getType();
        assert ty == DafnyParser.METHOD || ty == DafnyParser.FUNCTION;

        String name = declRef.getChild(0).getText();
        Tree parent = declRef.getParent();
        if (parent.getType() == DafnyParser.CLASS) {
            DafnyClass clss = project.getClass(parent.getChild(0).getText());
            if (ty == DafnyParser.METHOD) {
                return clss.getMethod(name);
            } else {
                return clss.getFunction(name);
            }
        } else {
            if (ty == DafnyParser.METHOD) {
                return project.getMethod(name);
            } else {
                return project.getFunction(name);
            }
        }
    }


    /*
     * This visitor allows one to find all referenced methods and functions
     * used within a method/function body.
     *
     * TODO Refactor this using the class Callgraph. And use this code in Callgraph.
     */
    private class Visitor extends DafnyTreeDefaultVisitor<Void, DafnyDecl> {

        @Override
        public Void visitDefault(DafnyTree t, DafnyDecl arg) {
            for (DafnyTree child : t.getChildren()) {
                child.accept(this, arg);
            }
            return null;
        }

        @Override
        public Void visitCALL(DafnyTree t, DafnyDecl enclosing) {
            add(callMap, enclosing, t);
            DafnyDecl decl = getDecl(t);
            add(callSiteMap, decl, t);

            return super.visitCALL(t, enclosing);
        }
    }

    private void add(Map<DafnyDecl, List<DafnyTree>> map, DafnyDecl decl, DafnyTree t) {
        List<DafnyTree> list = map.get(decl);
        if (list == null) {
            list = new LinkedList<>();
            map.put(decl, list);
        }
        list.add(t);
    }

}
