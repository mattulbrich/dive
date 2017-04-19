/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.dafnystructures;

import java.util.HashMap;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.HistoryMap;

/**
 * This visitor class can be used to resolve identifiers in the AST.
 *
 * Type checking is not done in this pass.
 *
 * One entry point for the visitation is the method {@link #visitProject()} that
 * iterates over all class, method and function declarations.
 *
 * @author Mattias Ulbrich
 */
public class ReferenceResolutionVisitor extends DafnyTreeDefaultVisitor<Void, Void> {

    /**
     * The project whose references are to be resolved
     */
    private final Project project;

    /**
     * The map for identifier names to declaration trees.
     *
     * Variables, fields, parameters, local variables are referenced here.
     */
    private final HistoryMap<String, DafnyTree> identifierMap =
            new HistoryMap<>(new HashMap<>());

    /**
     * The map for identifiers to declaration trees for callable names.
     *
     * Functions and Methods are referenced here
     */
    private final HistoryMap<String, DafnyTree> callableMap =
            new HistoryMap<>(new HashMap<>());


    /**
     * Instantiates a new reference resolution visitor.
     *
     * @param project
     *            the non-<code>null</code> project to visit
     */
    public ReferenceResolutionVisitor(Project project) {
        this.project = project;

        project.getMethods().forEach(x -> callableMap.put(x.getName(), x.getRepresentation()));
        project.getFunctions().forEach(x -> callableMap.put(x.getName(), x.getRepresentation()));
    }

    /**
     * Visit all entities defined in the project.
     *
     * The project used in the constructor is used for traversal.
     */
    public void visitProject() {
        // TODO make this better as soon as there is access to all toplevel trees
        project.getClasses().forEach(this::visitAll);
        project.getMethods().forEach(this::visitAll);
        project.getFunctions().forEach(this::visitAll);
    }

    /*
     * Visit the declaration tree associated with the dafny declaration.
     */
    private <T extends DafnyDecl> void visitAll(T cl) {
        cl.getRepresentation().accept(this, null);
    }

    /*
     * Adds an exception to the pool of observed exceptions.
     */
    private void addException(DafnyException dafnyException) {
        // TODO Do what it is supposed to do, do not throw.
        System.err.println("Error in line " + dafnyException.getTree().getToken().getLine());
        throw new Error(dafnyException);
    }

    /*
     * visit children recursively
     */
    @Override
    public Void visitDefault(DafnyTree t, Void arg) {
        for (DafnyTree child : t.getChildren()) {
            child.accept(this, null);
        }
        return null;
    }

    // ==================================== Looking up

    /*
     * Look up an ID or raise an exception.
     */
    @Override
    public Void visitID(DafnyTree t, Void a) {
        String name = t.getText();
        DafnyTree idDef = identifierMap.get(name);
        if(idDef == null) {
            addException(new DafnyException("Unknown identifier: " + name, t));
        } else {
            t.setDeclarationReference(idDef);
        }
        return null;
    }

    /*
     * Look up an ID used in a call or raise an exception.
     */
    @Override
    public Void visitCALL(DafnyTree t, Void a) {
        String name = t.getChild(0).getText();
        DafnyTree callable = callableMap.get(name);
        if(callable == null) {
            addException(new DafnyException("Unknown method or function: " + name, t));
        } else {
            t.getChild(0).setDeclarationReference(callable);
        }

        // do not revisit the name.
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, null);
        }
        return null;
    }

    // ==================================== Visiting

    @Override
    public Void visitALL(DafnyTree t, Void a) {
        int rewindTo = identifierMap.getHistory();
        String boundVar = t.getChild(0).getText();
        identifierMap.put(boundVar, t);
        // do not revisit the name.
        for (int i = 2; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, null);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    @Override
    public Void visitEX(DafnyTree t, Void a) {
        int rewindTo = identifierMap.getHistory();
        String boundVar = t.getChild(0).getText();
        identifierMap.put(boundVar, t);
        // do not revisit the name.
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, null);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    @Override
    public Void visitVAR(DafnyTree t, Void a) {
        identifierMap.put(t.getChild(0).getText(), t);
        return null;
    }

    @Override
    public Void visitBLOCK(DafnyTree t, Void a) {
        int rewindTo = identifierMap.getHistory();
        super.visitBLOCK(t, a);
        identifierMap.rewindHistory(rewindTo);

        return null;
    }

    @Override
    public Void visitCLASS(DafnyTree t, Void a) {
        int rewindIdentifiersTo = identifierMap.getHistory();
        int rewindCallablesTo = callableMap.getHistory();

        String classname = t.getChild(0).getText();
        // TODO make this a lookup
        DafnyClass dafnyClass = project.getClasses().get(0);

        for(DafnyField field : dafnyClass.getFields()) {
            // TODO why is the representation the type?
            identifierMap.put(field.getName(), (DafnyTree) field.getRepresentation().getParent());
        }

        for(DafnyMethod method : dafnyClass.getMethods()) {
            callableMap.put(method.getName(), method.getRepresentation());
        }

        for(DafnyFunction function : dafnyClass.getFunctions()) {
            callableMap.put(function.getName(), function.getRepresentation());
        }

        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, null);
        }

        identifierMap.rewindHistory(rewindIdentifiersTo);
        callableMap.rewindHistory(rewindCallablesTo);
        return null;
    }

    /*
     * Do not visit the function name.
     *
     * But visit the parameter declarations!
     */
    @Override
    public Void visitFUNCTION(DafnyTree t, Void a) {
        int rewindTo = identifierMap.getHistory();
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, null);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    /*
     * Do not visit the method name.
     *
     * But visit the parameter declarations!
     */
    @Override
    public Void visitMETHOD(DafnyTree t, Void a) {
        int rewindTo = identifierMap.getHistory();
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, null);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

}
