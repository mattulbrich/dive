/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.HistoryMap;
import edu.kit.iti.algover.util.TreeUtil;
import nonnull.NonNull;
import org.antlr.runtime.tree.Tree;

import java.util.HashMap;
import java.util.List;

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
public class ReferenceResolutionVisitor
        extends DafnyTreeDefaultVisitor<Void, ReferenceResolutionVisitor.Mode> {

    /**
     * The project whose references are to be resolved.
     */
    private final Project project;
    /**
     * The map for identifier names to declaration trees.
     *
     * Variables, fields, parameters, local variables are referenced here.
     */
    private final HistoryMap<String, DafnyTree> identifierMap = new HistoryMap<>(new HashMap<>());
    ;
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
    private final TypeResolution typeResolution;

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
        this.typeResolution = new TypeResolution(getExceptions());
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

    /**
     * Visit the expression given expression in the context of the given class.
     * <p>
     * This means that all fields of the class can be accessed without receiver.
     *
     * @param expression the expression to resolve
     * @param classCtx   the name of the class to use as context
     */
    public void visitExpression(@NonNull DafnyTree expression, @NonNull String classCtx) {
        DafnyClass clazz = project.getClass(classCtx);
        int rewindIdentifiersTo = identifierMap.getHistory();
        int rewindCallablesTo = callableMap.getHistory();

        addClassEntitites(clazz);
        visitExpression(expression);

        identifierMap.rewindHistory(rewindIdentifiersTo);
        callableMap.rewindHistory(rewindCallablesTo);
    }

    /**
     * Visit an expression using this visitor.
     *
     * @param expression the expression to resolve
     */
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
                    new DafnyException("Name clash: Callable entity named "
                            + declName + " has already been defined.",
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

    // ==================================== Looking up

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

        // make sure that methods are not used in expressions.
        DafnyTree declaration = callID.getDeclarationReference();
        if(declaration != null && declaration.getType() == DafnyParser.METHOD) {
            Tree parent = t.getParent();
            if (parent.getType() != DafnyParser.BLOCK
                    && parent.getType() != DafnyParser.ASSIGN
                    && parent.getType() != DafnyParser.VAR) {
                // assign and var have it is the last element ensured by parser.
                addException(new DafnyException("Method calls must not be used in expressions", t));
            }
        }


        // do not revisit the name.
        for (DafnyTree arg : t.getFirstChildWithType(DafnyParser.ARGS).getChildren()) {
            arg.accept(this, a);
        }
        return null;
    }

    /*
     * resolve the name of the class and the constructor method.
     */
    @Override
    public Void visitNEW(DafnyTree t, Mode mode) {
        DafnyTree type;
        DafnyTree call = null;
        DafnyTree size = null;

        DafnyTree child = t.getChild(0);
        switch (child.getType()) {
        case DafnyParser.ID:
            call = t.getFirstChildWithType(DafnyParser.CALL);
            type = child;
            break;
        case DafnyParser.ARRAY_ACCESS:
            type = child.getChild(0);
            size = child.getChild(1);
            break;
        default:
            throw new Error("Unexpected new construct " + t);
        }

        type.accept(this, Mode.TYPE);

        if (call != null) {
            // TODO This will not work for parametrised classes ...
            String name = child.getText();
            DafnyClass clazz = project.getClass(name);
            if (clazz == null) {
                addException(new DafnyException("Unknown class: " + type, t));
                return null;
            }
            DafnyMethod method = clazz.getMethod(call.getChild(0).getText());
            if (method == null) {
                addException(new DafnyException("Unknown method " + call.getChild(0).getText() +
                        " in class " + type, t));
                return null;
            }
            call.getChild(0).setDeclarationReference(method.getRepresentation());
        }

        if(size != null) {
            size.accept(this, Mode.EXPR);
        }

        return null;
    }

    /*
     * Temporarily add quantified variable, visit matrix and remove variable.
     */
    @Override
    public Void visitALL(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        for (int i = 0; i < t.getChildCount()-2; i++) {
            String boundVar = t.getChild(i).getText();
            identifierMap.put(boundVar, t);
            // do not revisit the name.
        }
        t.getFirstChildWithType(DafnyParser.TYPE).accept(this, Mode.TYPE);
        t.getLastChild().accept(this, Mode.EXPR);
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    @Override
    public Void visitEX(DafnyTree t, Mode a) {
        // Reuse the code for universal quantifier.
        return visitALL(t, a);
    }

    /*
     * Temporarily add quantified variable(s), visit matrix and remove variable.
     */
    @Override
    public Void visitLET(DafnyTree t, Mode a) {
        int rewindTo = identifierMap.getHistory();
        List<DafnyTree> vars = t.getFirstChildWithType(DafnyParser.VAR).getChildren();
        for (DafnyTree boundVar : vars) {
            identifierMap.put(boundVar.getText(), t);
        }
        // do not revisit the variables.
        for (int i = 1; i < t.getChildCount(); i++) {
            t.getChild(i).accept(this, a);
        }
        identifierMap.rewindHistory(rewindTo);
        return null;
    }

    /*
     * Temporarily add quantified variable, visit matrix and remove variable.
     */
    // ==================================== Visiting

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
        // bugfix #44
        DafnyTree ty = t.getFirstChildWithType(DafnyParser.TYPE);
        if(ty != null) {
            ty.accept(this, Mode.TYPE);
        }
        if (t.getLastChild().getType() != DafnyParser.TYPE) {
            t.getLastChild().accept(this, Mode.EXPR);
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
    }

}