package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;

import java.util.LinkedList;
import java.util.List;

/**
 * Visitor implementation for DafnyTrees. Visits each node of a DafnyTree and cerates DafnyDecl Objects
 *
 */
public class DafnyTreeVisitorImpl<DafnyDecl, A> extends DafnyTreeDefaultVisitor<DafnyDecl, A> {


    @Override
    public DafnyDecl visitCLASS(DafnyTree t, A a) {
        DafnyClassBuilder dcb = new DafnyClassBuilder();

        //create lists for different members of a class
        List<DafnyField> fields = new LinkedList<>();
        List<DafnyFunction> functions = new LinkedList<>();
        List<DafnyMethod> methods = new LinkedList<>();

        List<DafnyTree> fieldsAsTree = t.getChildrenWithType(DafnyParser.FIELD);
        for (DafnyTree tree: fieldsAsTree) {
            fields.add((DafnyField) visitFIELD(tree, a));
        }

        List<DafnyTree> functionsAsTree = t.getChildrenWithType(DafnyParser.FUNCTION);
        for (DafnyTree tree: functionsAsTree) {
           functions.add((DafnyFunction) visitFUNCTION(tree, a));
        }

        List<DafnyTree> methodsAsTree = t.getChildrenWithType(DafnyParser.METHOD);
        for (DafnyTree tree: methodsAsTree) {
            methods.add((DafnyMethod) visitMETHOD(tree, a));
        }

        dcb.setName(t.getChild(0).getText()).setFields(fields).setFunctions(functions).setMethods(methods);
        return null;
    }

    @Override
    public DafnyDecl visitFIELD(DafnyTree t, A a) {
        return (DafnyDecl) new DafnyField(t.getChild(1), t.getChild(0).getText());
    }

    @Override
    public DafnyDecl visitFUNCTION(DafnyTree t, A a) {

        List<DafnyTree> params = t.getFirstChildWithType(DafnyParser.ARGS).getChildrenWithType(DafnyParser.VAR);

        DafnyFunction func = new DafnyFunction(t.getChild(0).getText(),
                params,
                t.getFirstChildWithType(DafnyParser.RETURNS),
                t.getFirstChildWithType(DafnyParser.BLOCK));

        return (DafnyDecl) func;
    }

    @Override
    public DafnyDecl visitMETHOD(DafnyTree t, A a) {
        List<DafnyTree> params = t.getFirstChildWithType(DafnyParser.ARGS).getChildrenWithType(DafnyParser.VAR);

        DafnyMethod meth = new DafnyMethod(t.getChild(0).getText(),
                params,
                t.getChildrenWithType(DafnyParser.RETURNS),
                t.getFirstChildWithType(DafnyParser.BLOCK),
                t.getChildrenWithType(DafnyParser.REQUIRES),
                t.getChildrenWithType(DafnyParser.ENSURES)
                );

        return (DafnyDecl) meth;


    }


}

