/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.util.List;

import edu.kit.iti.algover.project.Project;

public class TypeResolution extends DafnyTreeDefaultVisitor<DafnyTree, Void> {

    private List<DafnyException> exceptions;

    private DafnyTree UNKNOWN_TYPE = new DafnyTree(DafnyParser.ID, "UNKNOWN_TYPE");

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

        assert ref.getType() == DafnyParser.VAR || ref.getType() == DafnyParser.FIELD;
        DafnyTree type = ref.getLastChild();
        t.setExpressionType(type);
        return type;
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
        if(tree.getChildCount() > 2) {
            tree.getChild(2).accept(this, null);
        }
        return null;
    }

    // ------------------- INT operations

    private DafnyTree intOperation(DafnyTree t) {
        DafnyTree storedType = t.getExpressionType();
        if(storedType != null) {
            return storedType;
        }

        if(t.getChildCount() == 0) {
            return new DafnyTree(DafnyParser.INT);
        }

        DafnyTree result = null;
        for (int i = 0; i < t.getChildCount(); i++) {
            result = t.getChild(i).accept(this, null);
            if(result.getType() != DafnyParser.INT) {
                exceptions.add(new DafnyException("Wrong type. Expected int but got " + result,
                        t.getChild(i)));
            }
        }

        return result;
    }

    @Override
    public DafnyTree visitPLUS(DafnyTree t, Void a) {
        return intOperation(t);
    }

    @Override
    public DafnyTree visitTIMES(DafnyTree t, Void a) {
        return intOperation(t);
    }

    @Override
    public DafnyTree visitMINUS(DafnyTree t, Void a) {
        return intOperation(t);
    }

    @Override
    public DafnyTree visitINT_LIT(DafnyTree t, Void a) {
        return intOperation(t);
    }

    // ------------------- Bool operations

    private DafnyTree boolOperation(DafnyTree t) {
        DafnyTree storedType = t.getExpressionType();
        if(storedType != null) {
            return storedType;
        }

        if(t.getChildCount() == 0) {
            return new DafnyTree(DafnyParser.BOOL);
        }

        DafnyTree result = null;
        for (int i = 0; i < t.getChildCount(); i++) {
            result = t.getChild(i).accept(this, null);
            if(result.getType() != DafnyParser.BOOL) {
                exceptions.add(new DafnyException("Wrong type. Expected bool but got " + result,
                        t.getChild(i)));
            }
        }

        return result;
    }

    @Override
    public DafnyTree visitAND(DafnyTree t, Void a) {
        return boolOperation(t);
    }

    @Override
    public DafnyTree visitOR(DafnyTree t, Void a) {
        return boolOperation(t);
    }

    @Override
    public DafnyTree visitIMPLIES(DafnyTree t, Void a) {
        return boolOperation(t);
    }

    @Override
    public DafnyTree visitNOT(DafnyTree t, Void a) {
        return boolOperation(t);
    }

    // Comparisons

    @Override
    public DafnyTree visitALL(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitALL(t, a);
    }

    @Override
    public DafnyTree visitEX(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitEX(t, a);
    }

    @Override
    public DafnyTree visitEQ(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitEQ(t, a);
    }

    @Override
    public DafnyTree visitLE(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitLE(t, a);
    }

    @Override
    public DafnyTree visitLT(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitLT(t, a);
    }

    @Override
    public DafnyTree visitGE(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitGE(t, a);
    }

    @Override
    public DafnyTree visitGT(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitGT(t, a);
    }




    @Override
    public DafnyTree visitLENGTH(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitLENGTH(t, a);
    }



    @Override
    public DafnyTree visitARRAY_ACCESS(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitARRAY_ACCESS(t, a);
    }

    @Override
    public DafnyTree visitCALL(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitCALL(t, a);
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

        DafnyTree result = fieldDecl.getChild(1);
        t.setExpressionType(result);
        return result;
    }

    @Override
    public DafnyTree visitINTERSECT(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitINTERSECT(t, a);
    }

    @Override
    public DafnyTree visitLISTEX(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitLISTEX(t, a);
    }

    @Override
    public DafnyTree visitNEQ(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitNEQ(t, a);
    }

    @Override
    public DafnyTree visitNOETHER_LESS(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitNOETHER_LESS(t, a);
    }

    @Override
    public DafnyTree visitNULL(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitNULL(t, a);
    }

    @Override
    public DafnyTree visitSETEX(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitSETEX(t, a);
    }

    @Override
    public DafnyTree visitTHIS(DafnyTree t, Void a) {
        DafnyTree clzz = (DafnyTree) t.getAncestor(DafnyParser.CLASS);
        if(clzz == null) {
            exceptions.add(new DafnyException("Unexpected this reference outside class definition", t));
            return UNKNOWN_TYPE;
        }
        t.setExpressionType(clzz.getChild(0));
        return t.getExpressionType();
    }

    @Override
    public DafnyTree visitUNION(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitUNION(t, a);
    }

    @Override
    public DafnyTree visitWILDCARD(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitWILDCARD(t, a);
    }

    @Override
    public DafnyTree visitNIL(DafnyTree t, Void a) {
        // TODO Auto-generated method stub
        return super.visitNIL(t, a);
    }


    @Override
    public DafnyTree visitASSIGN(DafnyTree t, Void a) {
        return visitDepth(t);
    }

    @Override
    public DafnyTree visitBLOCK(DafnyTree t, Void a) {
        return visitDepth(t);
    }

}
