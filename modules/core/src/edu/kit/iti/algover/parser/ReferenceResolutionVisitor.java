/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import java.util.HashMap;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.HistoryMap;
import edu.kit.iti.algover.util.TreeUtil;

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
public class ReferenceResolutionVisitor extends DafnyTreeDefaultVisitor<Void, ReferenceResolutionVisitor.Mode> {

    /**
     * The project whose references are to be resolved.
     */
    private final Project project;

    /**
     * The two modes of this visitor.
     */
    public static enum Mode {
        /**
         * Used when expressions are being visited. All identifiers refer to
         * variables/fields.
         */
        EXPR,
        /**
         * Used when types are being visited. All identifiers refer to class
         * names.
         */
        TYPE
    };

    /**
     * The map for identifier names to declaration trees.
     *
     * Variables, fields, parameters, local variables are referenced here.
     */
    private final HistoryMap<String, DafnyTree> identifierMap = new HistoryMap<>(new HashMap<>());

    /**
     * The map for identifiers to declaration trees for callable names.
     *
     * Functions and Methods are referenced here
     */
    private final HistoryMap<String, DafnyTree> callableMap = new HistoryMap<>(new HashMap<>());

    /**
     * The exceptions collected during visitation, may be <code>null</code>.
     */
    private final List<DafnyException> exceptions;

    /**
     * The type resolution is needed for resolving fields.
     */
    private final TypeResolution typeResolution = new TypeResolution(getExceptions());

    /**
     * Instantiates a new reference resolution visitor.
     *
     * @param project
     *            the non-<code>null</code> project to visit
     * @param exceptions
     *            the list to which exceptions are reported, may be
     *            <code>null</code>
     */
    public ReferenceResolutionVisitor(Project project, List<DafnyException> exceptions) {
        this.project = project;
        this.exceptions = exceptions;
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

        // TODO make this better as soon as there is access to all toplevel
        // trees
        project.getClasses().forEach(this::visitAll);
        project.getMethods().forEach(this::visitAll);
        project.getFunctions().forEach(this::visitAll);
    }

    public void visitExpression(DafnyTree expression, String classCtx) {
        DafnyClass clazz = project.getClass(classCtx);
        int rewindIdentifiersTo = identifierMap.getHistory();
        int rewindCallablesTo = callableMap.getHistory();

        addClassEntitites(clazz);
        visitExpression(expression);

        identifierMap.rewindHistory(rewindIdentifiersTo);
        callableMap.rewindHistory(rewindCallablesTo);
    }

    public void visitExpression(DafnyTree expression) {
        expression.accept(this, Mode.EXPR);
    }

    public List<DafnyException> getExceptions() {
        return exceptions;
    }

    private void addToCallableMap(DafnyDecl decl) {
        String declName = decl.getName();
        if (callableMap.containsKey(declName)) {
            addException(
                    new DafnyException("Name clash: Callable entity named " + declName + " has already been defined.",
                            decl.getRepresentation()));
            return;
        }
        callableMap.put(declName, decl.getRepresentation());
    }

    private void addClassEntitites(DafnyClass dafnyClass) {
        for (DafnyField field : dafnyClass.getFields()) {
            identifierMap.put(field.getName(), field.getRepresentation());
        }

        for (DafnyMethod method : dafnyClass.getMethods()) {
            callableMap.put(method.getName(), method.getRepresentation());
        }

        for (DafnyFunction function : dafnyClass.getFunctions()) {
            callableMap.put(function.getName(), function.getRepresentation());
        }
    }

    /*
     * Visit the declaration tree associated with the dafny declaration.
     */
    private <T extends DafnyDecl> void visitAll(T cl) {
        cl.getRepresentation().accept(this, Mode.EXPR);
    }

    /*
     * Adds an exception to the pool of observed exceptions.
     */
    private void addException(DafnyException dafnyException) {
        if (exceptions != null) {
            exceptions.add(dafnyException);
        }
    }

    /*
     * visit children recursively
     */
    @Override
    public Void visitDefault(DafnyTree t, Mode arg) {
        for (DafnyTree child : t.getChildren()) {
            child.accept(this, arg);
        }
        return null;
    }

    // ==================================== Looking up

    /*
     * Look up an ID or raise an exception.
     */
    @Override
    public Void visitID(DafnyTree t, Mode mode) {
        String name = t.getText();
        switch (mode) {
        case EXPR:
            DafnyTree idDef = identifierMap.get(name);
            if (idDef == null) {
                addException(new DafnyException("Unknown identifier: " + name, t));
            } else {
                t.setDeclarationReference(idDef);
            }
            break;
        case TYPE:
            DafnyClass classDef = project.getClass(name);
            if (classDef == null) {
                addException(new DafnyException("Unknown class identifier: " + name, t));
            } else {
                t.setDeclarationReference(classDef.getRepresentation());
            }
            break;
        default:
            throw new Error();
        }
        return null;
    }

    /*
     * Look up the field name of the receiver in the corresponding class ...
     */
    @Override
    public Void visitFIELD_ACCESS(DafnyTree t, Mode a) {
        DafnyTree receiver = t.getChild(0);
        DafnyTree field = t.getChild(1);

        receiver.accept(this, a);
        String type = TreeUtil.toTypeString(receiver.accept(typeResolution, null));
        DafnyClass clazz = project.getClass(type);
        if (clazz == null) {
            addException(new DafnyException("Unknown class: " + type, receiver));
            return null;
        }

        DafnyField fieldDecl = clazz.getField(field.getText());
        if (fieldDecl == null) {
            addException(new DafnyException("Unknown field " + field + " in class " + type, field));
            return null;
        }

        field.setDeclarationReference(fieldDecl.getRepresentation());
        return null;
    }

    /*
     * Look up an ID used in a call or raise an exception.
     */
    @Override
    public Void visitCALL(DafnyTree t, Mode a) {
        DafnyTree callID = t.getChild(0);
        String name = callID.getText();
        boolean hasReceiver = t.getChildCount() > 2;

        if (hasReceiver) {
            DafnyTree receiver = t.getChild(1);
            receiver.accept(this, Mode.EXPR);
            String type = TreeUtil.toTypeString(receiver.accept(typeResolution, null));

            DafnyClass clazz = project.getClass(type);
            if (clazz == null) {
                addException(new DafnyException("Unknown class: " + type, receiver));
                return null;
            }

            DafnyDecl callable = clazz.getMethod(name);
            if (callable == null) {
                callable = clazz.getFunction(name);
            }
            if (callable == null) {
                addException(new DafnyException("Unknown method or function "
                            + name + " in class " + type, callID));
                return null;
            }

            callID.setDeclarationReference(callable.getRepresentation());
        } else {
            DafnyTree callable = callableMap.get(name);
            if (callable == null) {
                addException(new DafnyException("Unknown method or function: " + name, callID));
            } else {
                callID.setDeclarationReference(callable);
            }
        }

        // do not revisit the name.
        for (DafnyTree arg : t.getFirstChildWithType(DafnyParser.ARGS).getChildren()) {
            arg.accept(this, a);
        }
        return null;
    }

    // ==================================== Visiting

    /*
     * Temporarily add quantified variable, visit matrix and remove variable.
     */
    @Override
    public Void visitALL(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        String boundVar = t.getChild(0).getText();
        identifierMap.put(boundVar, t);
        // do not revisit the name.
        for (int i = 2; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, a);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    /*
     * Temporarily add quantified variable, visit matrix and remove variable.
     */
    @Override
    public Void visitEX(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        String boundVar = t.getChild(0).getText();
        identifierMap.put(boundVar, t);
        // do not revisit the name.
        t.getChild(1).accept(this, Mode.TYPE);
        t.getChild(2).accept(this, Mode.EXPR);
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    /*
     * Remember the rewind position for the block and rewind after visitation.
     */
    @Override
    public Void visitBLOCK(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        super.visitBLOCK(t, a);
        identifierMap.rewindHistory(rewindTo);

        return null;
    }

    @Override
    public Void visitCLASS(DafnyTree t, Mode a) {
        int rewindIdentifiersTo = identifierMap.getHistory();
        int rewindCallablesTo = callableMap.getHistory();

        String classname = t.getChild(0).getText();
        DafnyClass dafnyClass = project.getClass(classname);

        addClassEntitites(dafnyClass);

        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, a);
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
    public Void visitFUNCTION(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, i == 2 ? Mode.TYPE : a);
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
    public Void visitMETHOD(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, a);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    /*
     * Do not visit the label name.
     *
     * Eventually a list of defined labels could be kept to avoid double
     * declaration.
     */
    @Override
    public Void visitLABEL(DafnyTree t, Mode a) {
        return null;
    }

    /*
     * Just add the declared variable to the identifierMap.
     * Resolve the type.
     */
    @Override
    public Void visitVAR(DafnyTree t, Mode a) {
        identifierMap.put(t.getChild(0).getText(), t);
        t.getChild(1).accept(this, Mode.TYPE);
        if (t.getChildCount() > 2) {
            t.getChild(2).accept(this, Mode.EXPR);
        }
        return null;
    }

    /*
     * Visit the type in type mode.
     *
     * Do not visit the field name.
     */
    @Override
    public Void visitFIELD(DafnyTree t, Mode a) {
        t.getChild(1).accept(this, Mode.TYPE);
        return null;
    }

    @Override
    public Void visitARRAY(DafnyTree t, Mode mode) {
        assert mode == Mode.TYPE;
        t.getChild(0).accept(this, mode);
        return null;
    }

}