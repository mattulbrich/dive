/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.util.List;

import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Util;
import org.antlr.runtime.tree.Tree;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TreeUtil;

public class TypeResolution extends DafnyTreeDefaultVisitor<DafnyTree, Void> {

    private static final DafnyTree INT_TYPE = new DafnyTree(DafnyParser.INT, "int");
    private static final DafnyTree UNKNOWN_TYPE = new DafnyTree(DafnyParser.ID, "UNKNOWN_TYPE");
    private static final DafnyTree BOOL_TYPE = new DafnyTree(DafnyParser.BOOL, "bool");
    private static final DafnyTree OBJECT_TYPE = new DafnyTree(DafnyParser.ID, "object");;

    private List<DafnyException> exceptions;

    public TypeResolution(List<DafnyException> exceptions) {
        this.exceptions = exceptions;
    }

    public void visitProject(Project project) {
        project.getClasses().forEach(x -> x.getRepresentation().accept(this, null));
        project.getMethods().forEach(x -> x.getRepresentation().accept(this, null));
        project.getFunctions().forEach(x -> x.getRepresentation().accept(this, null));
    }


    private DafnyTree visitDepth(DafnyTree tree, int startat) {
        for (int i = startat; i < tree.getChildCount(); i++) {
            tree.getChild(i).accept(this, null);
        }
        return null;
    }


    private DafnyTree visitDepth(DafnyTree tree) {
        return visitDepth(tree, 0);
    }

    @Override
    public DafnyTree visitDefault(DafnyTree t, Void arg) {
        return t.getExpressionType();
    }

    @Override
    public DafnyTree visitID(DafnyTree t, Void a) {
        DafnyTree storedType = t.getExpressionType();
        if(storedType != null) {
            return storedType;
        }

        DafnyTree ref = t.getDeclarationReference();
        if (ref == null) {
            exceptions.add(new DafnyException("Unresolved identifier " + t.getText(), t));
            return UNKNOWN_TYPE;
        }

        switch (ref.getType()) {
        case DafnyParser.VAR:
        case DafnyParser.FIELD:
        case DafnyParser.ALL:
        case DafnyParser.EX:
            DafnyTree typeTree = ref.getFirstChildWithType(DafnyParser.TYPE);
            if (typeTree == null) {
                // this is the case for "var i := 0" if ref has not been visited by type resolution, yet.
                ref.accept(this, a);
                typeTree = ref.getFirstChildWithType(DafnyParser.TYPE);
            }
            DafnyTree type = typeTree.getChild(0);
            t.setExpressionType(type);
            return type;

        case DafnyParser.LET:
            // find the relative number of variable and take type of appropriate expression
            DafnyTree vars = ref.getChild(0);
            for (int i = 0; i < vars.getChildCount(); i++) {
                if(vars.getChild(i).getText().equals(t.getText())) {
                    DafnyTree ty = ref.getChild(i + 1).getExpressionType();
                    t.setExpressionType(ty);
                    return ty;
                }
            }

        default:
            throw new Error("Should not be reachable " + ref.getType());
        }
    }

    // ------------------- structural visitation
    @Override
    public DafnyTree visitCLASS(DafnyTree tree, Void a) {
        return visitDepth(tree, 1);
    }

    @Override
    public DafnyTree visitFUNCTION(DafnyTree tree, Void a) {
        return visitDepth(tree, 1);
    }

    @Override
    public DafnyTree visitMETHOD(DafnyTree tree, Void a) {
        return visitDepth(tree, 1);
    }

    @Override
    public DafnyTree visitVAR(DafnyTree tree, Void a) {
        if(tree.getLastChild().getType() != DafnyParser.TYPE) {
            // this is a variable declaration with assignment ...
            DafnyTree ty = tree.getLastChild().accept(this, null);
            DafnyTree explicitType = tree.getFirstChildWithType(DafnyParser.TYPE);
            if (explicitType != null) {
                String ty1 = TreeUtil.toTypeString(explicitType.getChild(0));
                String ty2 = TreeUtil.toTypeString(ty);
                // TODO FIXME CAUTION: Subtyping
                if(!ty1.equals(ty2)) {
                    exceptions.add(new DafnyException("Assigning a value of type " + ty2 + " to an entitity"
                            + " of type " + ty1, tree));
                }
            } else {
                // if no explicit type, add it as artificial element
                DafnyTree newTyNode = new DafnyTree(DafnyParser.TYPE);
                newTyNode.addChild(ty.dupTree());
                tree.insertChild(tree.getChildCount() - 1, newTyNode);
            }
        }
        return null;
    }

    // ------------------- INT operations

    //TODO DOC THIS
    private DafnyTree operation(DafnyTree tree, DafnyTree resultType, String... expectedArgTypes) {
        DafnyTree storedType = tree.getExpressionType();
        if(storedType != null) {
            return storedType;
        }

        for (int i = 0; i < tree.getChildCount(); i++) {
            DafnyTree childType = tree.getChild(i).accept(this, null);
            if (i < expectedArgTypes.length && childType != null) {
                String typeString = TreeUtil.toTypeString(childType);
                if (!expectedArgTypes[i].equals(typeString)) {
                    exceptions.add(
                            new DafnyException("Wrong type. Expected " + expectedArgTypes[i]
                                    + " but got " + typeString,
                                    tree.getChild(i)));
                }
            }
        }

        tree.setExpressionType(resultType);
        return resultType;
    }

    @Override
    public DafnyTree visitPLUS(DafnyTree t, Void a) {
        return operation(t, INT_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitTIMES(DafnyTree t, Void a) {
        return operation(t, INT_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitDIV(DafnyTree t, Void a) {
        return operation(t, INT_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitMINUS(DafnyTree t, Void a) {
        return operation(t, INT_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitINT_LIT(DafnyTree t, Void a) {
        return operation(t, INT_TYPE);
    }

    // ------------------- Bool operations

    @Override
    public DafnyTree visitAND(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "bool", "bool");
    }

    @Override
    public DafnyTree visitOR(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "bool", "bool");
    }

    @Override
    public DafnyTree visitIMPLIES(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "bool", "bool");
    }

    @Override
    public DafnyTree visitNOT(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "bool");
    }

    @Override
    public DafnyTree visitTRUE(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE);
    }

    @Override
    public DafnyTree visitFALSE(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE);
    }

    // Comparisons

    @Override
    public DafnyTree visitALL(DafnyTree t, Void a) {
        DafnyTree matrixTy = t.getLastChild().accept(this, null);
        if (!matrixTy.equals(BOOL_TYPE)) {
            exceptions.add(new DafnyException("Matrix of a quantifier must be Boolean", t));
        }
        return BOOL_TYPE;
    }

    @Override
    public DafnyTree visitEX(DafnyTree t, Void a) {
        DafnyTree matrixTy = t.getLastChild().accept(this, null);
        if (!matrixTy.equals(BOOL_TYPE)) {
            exceptions.add(new DafnyException("Matrix of a quantifier must be Boolean", t));
        }
        return BOOL_TYPE;
    }

    @Override
    public DafnyTree visitLET(DafnyTree t, Void a) {

        // do not visit the list of variables!
        for (int i = 1; i < t.getChildCount(); i++) {
            DafnyTree child = t.getChild(i);
            child.accept(this, null);
        }
        return t.getLastChild().getExpressionType();
    }


    @Override
    public DafnyTree visitEQ(DafnyTree t, Void a) {
        operation(t, BOOL_TYPE);
        String ty1 = TreeUtil.toTypeString(t.getChild(0).getExpressionType());
        String ty2 = TreeUtil.toTypeString(t.getChild(1).getExpressionType());

        if (!ty1.equals(ty2)) {
            exceptions.add(new DafnyException("Equality can only be applied to equally typed terms", t));
        }

        return BOOL_TYPE;
    }

    @Override
    public DafnyTree visitNEQ(DafnyTree t, Void a) {
        return visitEQ(t, a);
    }


    @Override
    public DafnyTree visitLE(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitLT(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitGE(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitGT(DafnyTree t, Void a) {
        return operation(t, BOOL_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitLENGTH(DafnyTree t, Void a) {
        DafnyTree arg = t.getChild(0);
        DafnyTree type = arg.accept(this, null);

        if (type.getType() != DafnyParser.ARRAY &&
            type.getType() != DafnyParser.SEQ) {
            exceptions.add(new DafnyException(
                    "Only arrays and sequences have a length", t));
        }

        t.setExpressionType(INT_TYPE);
        return INT_TYPE;
    }

    @Override
    public DafnyTree visitARRAY_ACCESS(DafnyTree t, Void a) {
        DafnyTree receiver = t.getChild(0);
        DafnyTree index = t.getChild(1);

        DafnyTree recvType = receiver.accept(this, null);
        DafnyTree indexType = index.accept(this, null);

        if (indexType.getType() != DafnyParser.INT) {
            exceptions.add(new DafnyException(
                    "Array index not of type int, but " + indexType, index));
        }

        if (recvType.getType() != DafnyParser.ARRAY &&
            recvType.getType() != DafnyParser.SEQ) {
            exceptions.add(new DafnyException(
                    "Only arrays or sequences can be indexed", t));
            // set a fake type to avoid internal exceptions when continuing
            DafnyTree ty = ASTUtil.id("<unknownType>");
            t.setExpressionType(ty);
            return ty;
        }

        DafnyTree ty = recvType.getChild(0);
        t.setExpressionType(ty);
        return ty;
    }

    @Override
    public DafnyTree visitCALL(DafnyTree t, Void a) {
        DafnyTree call = t.getChild(0);
        DafnyTree decl = call.getDeclarationReference();

        assert decl != null:
            "ReferenceResolutionVisitor must be run before the type resolution";

        Tree parent = decl.getParent();
        if(t.getChildCount() == 3) {
            // explicit receiver
            DafnyTree receiver = t.getChild(1);
            String recType = TreeUtil.toTypeString(receiver.accept(this, null));
            String expectedRecType = parent.getChild(0).getText();
            if(!recType.equals(expectedRecType)) {
                exceptions.add(new DafnyException("xxx", t));
            }
        }

        List<DafnyTree> actual = t.getFirstChildWithType(DafnyParser.ARGS).getChildren();
        List<DafnyTree> formal = decl.getFirstChildWithType(DafnyParser.ARGS).getChildren();

        if(formal.size() != actual.size()) {
            exceptions.add(new DafnyException("Wrong number of arguments in call to " +
                    call.getText() + ". Expected " + formal.size() +
                    ", but received " + actual.size(), t));
        }

        for (int i = 0; i < formal.size(); i++) {
            String act = TreeUtil.toTypeString(actual.get(i).accept(this, null));
            String expected = TreeUtil.toTypeString(formal.get(i).getFirstChildWithType(DafnyParser.TYPE).getChild(0));

            if (!act.equals(expected)) {
                exceptions.add(new DafnyException(
                        String.format("Wrong type for argument %d in "
                                + "call to %s. Expected %s, but got %s.",
                                i+1, call.getText(), expected, act), t));
            }
        }

        DafnyTree result;
        if(decl.getType() == DafnyParser.METHOD) {
            DafnyTree rets = decl.getFirstChildWithType(DafnyParser.RETURNS);
            if(rets == null) {
                result = null;
            } else {
                if(rets.getChildCount() > 1) {
                    List<DafnyTree> types = Util.map(rets.getChildren(),
                            x -> x.getFirstChildWithType(DafnyParser.TYPE).getChild(0));
                    result = ASTUtil.listExpr(types);
                } else {
                    result = rets.getChild(0).getFirstChildWithType(DafnyParser.TYPE).getChild(0);
                }
            }
        } else {
            assert decl.getType() == DafnyParser.FUNCTION;
            result = decl.getFirstChildWithType(DafnyParser.RETURNS).getChild(0);
        }
        t.setExpressionType(result);
        return result;
    }

    @Override
    public DafnyTree visitNEW(DafnyTree t, Void a) {
        if (t.getChild(0).getType() == DafnyParser.ARRAY_ACCESS) {
            DafnyTree size = t.getChild(0).getChild(1);
            DafnyTree type = t.getChild(0).getChild(0);

            DafnyTree sizeType = size.accept(this, null);
            if (sizeType.getType() != DafnyParser.INT) {
                exceptions.add(new DafnyException(
                        "Array index not of type int, but " + sizeType, size));
            }

            DafnyTree ty = new DafnyTree(DafnyParser.ARRAY, "array");
            ty.addChild(type.dupTree());
            t.setExpressionType(ty);
            return ty;

        } else {

            DafnyTree clss = t.getChild(0).getDeclarationReference();
            assert clss.getType() == DafnyParser.CLASS;
            DafnyTree ty = clss.getChild(0);
            t.setExpressionType(ty);
            return ty;
        }
    }

    @Override
    public DafnyTree visitFIELD_ACCESS(DafnyTree t, Void a) {
        DafnyTree receiver = t.getChild(0);
        DafnyTree field = t.getChild(1);
        DafnyTree fieldDecl = field.getDeclarationReference();

        receiver.accept(this, null);
        assert fieldDecl != null:
            "ReferenceResolutionVisitor must be run before the type resolution";

        assert fieldDecl.getType() != DafnyParser.VAR:
            "Field decl must be a var decl";

        DafnyTree result = fieldDecl.getFirstChildWithType(DafnyParser.TYPE).getChild(0);
        t.setExpressionType(result);
        return result;
    }

    @Override
    public DafnyTree visitLISTEX(DafnyTree t, Void a) {
        throw new UnsupportedOperationException("not yet implemented");
    }

    @Override
    public DafnyTree visitNOETHER_LESS(DafnyTree t, Void a) {
        // TODO eventually generalize this ...
        return operation(t, BOOL_TYPE, "int", "int");
    }

    @Override
    public DafnyTree visitNULL(DafnyTree t, Void a) {
        DafnyTree parent = (DafnyTree) t.getParent();
        DafnyTree ty;
        DafnyTree otherTree;

        switch (parent.getType()) {
        case DafnyParser.ASSIGN:
            ty = parent.getChild(0).getExpressionType();
            assert parent.getChild(1) == t : "null must be 2nd child";
            t.setExpressionType(ty);
            // TODO This should be translation to sort and then check for classtype?
            if (ty.getType() != DafnyParser.ID) {
                exceptions.add(new DafnyException("assigning null to a non-reference entity", parent));
            }
            return ty;

        case DafnyParser.VAR:
            assert parent.getChild(2) == t : "null must be 3rd child";
            ty = parent.getFirstChildWithType(DafnyParser.TYPE).getChild(0);
            t.setExpressionType(ty);
            if (ty.getType() != DafnyParser.ID) {
                exceptions.add(new DafnyException("assigning null to a non-reference entity", parent));
            }
            return ty;

        case DafnyParser.EQ:
        case DafnyParser.NEQ:
            if (parent.getChild(0) == t) {
                otherTree = parent.getChild(1);
            } else {
                otherTree = parent.getChild(0);
            }
            if (otherTree.getType() == DafnyParser.NULL) {
                t.setExpressionType(OBJECT_TYPE);
                return OBJECT_TYPE;
            } else {
                ty = otherTree.accept(this, null);
                t.setExpressionType(ty);
                return ty;
            }

        default:
            throw new Error("unexpected null under type " + parent.getType());
        }
    }

    @Override
    public DafnyTree visitSETEX(DafnyTree t, Void a) {
        throw new UnsupportedOperationException("not yet implemented");
    }

    @Override
    public DafnyTree visitTHIS(DafnyTree t, Void a) {
        DafnyTree clzz = (DafnyTree) t.getAncestor(DafnyParser.CLASS);
        if (clzz == null) {
            exceptions.add(new DafnyException("Unexpected this reference outside class definition", t));
            return UNKNOWN_TYPE;
        }
        t.setExpressionType(clzz.getChild(0));
        return t.getExpressionType();
    }

    @Override
    public DafnyTree visitWILDCARD(DafnyTree t, Void a) {
        DafnyTree parent = (DafnyTree) t.getParent();
        switch (parent.getType()) {
        case DafnyParser.IF:
        case DafnyParser.WHILE:
            assert
              parent.getFirstChildWithType(DafnyParser.LABEL) == null
              ? parent.getChild(0) == t
              : parent.getChild(1) == t : "Wildcard must be first child";

            t.setExpressionType(BOOL_TYPE);
            return BOOL_TYPE;

        case DafnyParser.ASSIGN:
            assert parent.getChild(1) == t : "Wildcard must be 2nd child";
            DafnyTree receiverType = parent.getChild(0).getExpressionType();
            assert receiverType != null : "receiver type must already have been resolved";
            t.setExpressionType(receiverType);
            return receiverType;

        default:
            throw new Error("Should not be reachable by grammar");
        }
    }

    @Override
    public DafnyTree visitNIL(DafnyTree t, Void a) {
        throw new UnsupportedOperationException("not yet implemented");
    }

    @Override
    public DafnyTree visitASSIGN(DafnyTree t, Void a) {
        DafnyTree result = visitDepth(t);
        String ty1;
        if (t.getChildCount() == 2) {
            // single assignment x := term;
            ty1 = TreeUtil.toTypeString(t.getChild(0).getExpressionType());
        } else {
            // multi-return: x,y := M();
            List<DafnyTree> lhs = t.getChildren().subList(0, t.getChildCount() - 1);
            List<DafnyTree> types = Util.map(lhs, DafnyTree::getExpressionType);
            ty1 = TreeUtil.toTypeString(ASTUtil.listExpr(types));
        }

        String ty2 = TreeUtil.toTypeString(t.getLastChild().getExpressionType());
        if (!ty1.equals(ty2)) {
            exceptions.add(new DafnyException("Assigning a value of type " + ty2 + " to an entitity"
                    + " of type " + ty1, t));
        }
        return result;
    }

    @Override
    public DafnyTree visitBLOCK(DafnyTree t, Void a) {
        return visitDepth(t);
    }

    @Override
    public DafnyTree visitIF(DafnyTree t, Void a) {
        return operation(t, null, "bool");
    }

    @Override
    public DafnyTree visitWHILE(DafnyTree t, Void a) {
        return operation(t, null, "bool");
    }

    @Override
    public DafnyTree visitREQUIRES(DafnyTree t, Void a) {
        return operation(t, null, "bool");
    }

    @Override
    public DafnyTree visitENSURES(DafnyTree t, Void a) {
        return operation(t, null, "bool");
    }

    @Override
    public DafnyTree visitINVARIANT(DafnyTree t, Void a) {
        return operation(t, null, "bool");
    }

    @Override
    public DafnyTree visitDECREASES(DafnyTree t, Void a) {
        return operation(t, null, "int");
    }



}
