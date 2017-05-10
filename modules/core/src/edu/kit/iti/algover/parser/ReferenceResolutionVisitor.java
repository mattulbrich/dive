/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
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
     * The project whose references are to be resolved.
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

    private final List<DafnyException> exceptions = new ArrayList<>();

    private final TypeResolution typeResolution = new TypeResolution(getExceptions());


    /**
     * Instantiates a new reference resolution visitor.
     *
     * @param project
     *            the non-<code>null</code> project to visit
     */
    public ReferenceResolutionVisitor(Project project) {
        this.project = project;
    }

    /**
     * Visit all entities defined in the project.
     *
     * The project used in the constructor is used for traversal.
     *
     * @throws DafnyException
     *             if a name cannot be resolved, has wrong type, name clashes
     *             etc.
     */
    public void visitProject() {

        project.getMethods().forEach(this::addToCallableMap);
        project.getFunctions().forEach(this::addToCallableMap);

        // TODO make this better as soon as there is access to all toplevel trees
        project.getClasses().forEach(this::visitAll);
        project.getMethods().forEach(this::visitAll);
        project.getFunctions().forEach(this::visitAll);
    }

    public List<DafnyException> getExceptions() {
        return exceptions;
    }

    private void addToCallableMap(DafnyDecl decl) {
        String declName = decl.getName();
        if (callableMap.containsKey(declName)) {
            addException(new DafnyException("Name clash: Callable entity named " + declName
                    + " has already been defined.", decl.getRepresentation()));
            return;
        }
        callableMap.put(declName, decl.getRepresentation());
    }

    /*
     * Visit the declaration tree associated with the dafny declaration.
     */
    private <T extends DafnyDecl> void visitAll(T cl) {
        cl.getRepresentation().accept(this, null);
        // cl.getRepresentation().accept(typeResolver, null);
    }

    /*
     * Adds an exception to the pool of observed exceptions.
     */
    private void addException(DafnyException dafnyException) {
        getExceptions().add(dafnyException);
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
        if (idDef == null) {
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
        if (callable == null) {
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

    /*
     * Temporarily add quantified variable, visit matrix and remove variable.
     */
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

    /*
     * Temporarily add quantified variable, visit matrix and remove variable.
     */
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

    /*
     * Just add the declared variable to the identifierMap.
     */
    @Override
    public Void visitVAR(DafnyTree t, Void a) {
        identifierMap.put(t.getChild(0).getText(), t);
        return null;
    }

    /*
     * Remember the rewind position for the block and
     * rewind after visitation.
     */
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

        // TODO XXXProjectAccess must be removed ...
        XXXProjectAccess xproject = new XXXProjectAccess(project);

        String classname = t.getChild(0).getText();
        DafnyClass dafnyClass = xproject.getClass(classname);

        for (DafnyField field : dafnyClass.getFields()) {
            // TODO why is the representation the type?
            identifierMap.put(field.getName(), (DafnyTree) field.getRepresentation().getParent());
        }

        for (DafnyMethod method : dafnyClass.getMethods()) {
            callableMap.put(method.getName(), method.getRepresentation());
        }

        for (DafnyFunction function : dafnyClass.getFunctions()) {
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
