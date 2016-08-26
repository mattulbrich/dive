package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.List;

/**
 * Visitor implementation for DafnyTrees. Visits each node of a DafnyTree and cerates DafnyDecl Objects
 */
public class DafnyDeclVisitor {

    private ProjectBuilder projectBuilder;
    private DafnyClassBuilder classBuilder = null;
    private String filename;

    public DafnyDeclVisitor(ProjectBuilder projectBuilder, String filename){
        this.projectBuilder = projectBuilder;
        this.filename = filename;

    }
    public void visit(String filename, DafnyTree tree) {
        // imports ?
        //System.out.println(tree.getText());
        switch(tree.getType()){
            case DafnyParser.CLASS:
            visitCLASS(tree);
                break;
            case DafnyParser.FUNCTION:
                visitFUNCTION(tree);
                break;
            case DafnyParser.METHOD:
                System.out.println("Visiting Method");
                visitMETHOD(tree);
                break;
        }

/*
        for (DafnyTree t : tree.getChildrenWithType(DafnyParser.CLASS)) {
            System.out.println("Visit1");

            visitCLASS(t);
        }


        for (DafnyTree t : tree.getChildrenWithType(DafnyParser.FUNCTION)) {
            visitFUNCTION(t);
        }

        for (DafnyTree t : tree.getChildrenWithType(DafnyParser.METHOD)) {
            visitMETHOD(t);
        }
*/

    }

    private void visitCLASS(DafnyTree t) {
        DafnyClassBuilder dcb = new DafnyClassBuilder(filename, t);
        classBuilder = dcb;

        dcb.setName(t.getChild(0).getText());
        //System.out.println(t.getChild(0).getText());
        List<DafnyTree> fieldsAsTree = t.getChildrenWithType(DafnyParser.FIELD);
        for (DafnyTree tree : fieldsAsTree) {
            visitFIELD(tree);
        }

        List<DafnyTree> functionsAsTree = t.getChildrenWithType(DafnyParser.FUNCTION);
        for (DafnyTree tree : functionsAsTree) {
            visitFUNCTION(tree);
        }

        List<DafnyTree> methodsAsTree = t.getChildrenWithType(DafnyParser.METHOD);
        for (DafnyTree tree : methodsAsTree) {
            visitMETHOD(tree);
        }

        classBuilder = null;
        DafnyClass dc = dcb.buildClass();

        projectBuilder.addClass(dc);
    }

    private void visitFIELD(DafnyTree t) {
        assert classBuilder != null;
        classBuilder.addField(new DafnyField(t.getChild(1), t.getChild(0).getText()));
    }

    private void visitFUNCTION(DafnyTree t) {

        List<DafnyTree> params = t.getFirstChildWithType(DafnyParser.ARGS).getChildrenWithType(DafnyParser.VAR);

        DafnyFunction func = new DafnyFunction(
                filename, t,
                t.getChild(0).getText(),
                params,
                t.getFirstChildWithType(DafnyParser.RETURNS),
                t.getFirstChildWithType(DafnyParser.BLOCK),
                t.getChildrenWithType(DafnyParser.REQUIRES),
                t.getChildrenWithType(DafnyParser.ENSURES));

        if (classBuilder == null) {

            projectBuilder.addFunction(func);
        } else {
            classBuilder.addFunction(func);
        }

    }

    private void visitMETHOD(DafnyTree t) {
        List<DafnyTree> params = t.getFirstChildWithType(DafnyParser.ARGS).getChildrenWithType(DafnyParser.VAR);

        DafnyMethod meth = new DafnyMethod(filename, t, t.getChild(0).getText(),
                params,
                t.getChildrenWithType(DafnyParser.RETURNS),
                t.getFirstChildWithType(DafnyParser.BLOCK),
                t.getChildrenWithType(DafnyParser.REQUIRES),
                t.getChildrenWithType(DafnyParser.ENSURES)
        );


        if (classBuilder == null) {
            projectBuilder.addMethod(meth);
        } else {
            classBuilder.addMethod(meth);
        }

    }


}

