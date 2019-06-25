package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.ArrayList;
import java.util.List;

public class DafnyDeclStringVisitor implements DafnyDeclVisitor<String, Void> {

    @Override
    public String visit(DafnyClass cl, Void arg) {
        return "Class " + cl.getName();
    }

    @Override
    public String visit(DafnyMethod m, Void arg) {
        StringBuilder methodDeclaration = new StringBuilder();
        methodDeclaration.append("Method ");
        methodDeclaration.append(m.getName());
        List<DafnyTree> params = m.getParams();
        methodDeclaration.append("(");
        if (params.size() != 0) {
            for (DafnyTree parameter : params) {
                switch (parameter.getText()) {
                    case "VAR":

                    case "ARGS":
                }
            }
        }
        methodDeclaration.append(")");
        return methodDeclaration.toString();
    }

    @Override
    public String visit(DafnyFunction f, Void arg) {
        StringBuilder methodDeclaration = new StringBuilder();
        methodDeclaration.append("Function ");
        methodDeclaration.append(f.getName());
        List<DafnyTree> params = f.getParameters();
        methodDeclaration.append("(");
        if (params.size() != 0) {
            for (DafnyTree parameter : params) {
                switch (parameter.getText()) {
                    case "VAR":
                           /* methodDeclaration.append("Parameter ");
                            ArrayList<String> strings = new ArrayList<>();
                            if(parameter.getChildren() != null) {
                                parameter.getChildren().forEach(dafnyTree -> {
                                    strings.addAll(dafnyTree.accept(new DafnyTreeCallEntityVisitor(), null));
                                });
                            }
                            strings.forEach(s -> {
                                methodDeclaration.append(s);
                                methodDeclaration.append(" ");
                            });*/
                    case "ARGS":
                        methodDeclaration.append("Argument ");
                        ArrayList<String> stringA = new ArrayList<>();

                        parameter.getChildren().forEach(dafnyTree -> {
                            stringA.addAll(dafnyTree.accept(new CallDafnyTreeVisitor(), null));
                        });
                        stringA.forEach(s -> {
                            methodDeclaration.append(s);
                            methodDeclaration.append(" ");
                        });

                }
            }
        }
        methodDeclaration.append(")");
        if(f.getDecreasesClause() != null){
            methodDeclaration.append("\nDecreases ");
            List<DafnyTree> children = f.getDecreasesClause().getChildren();
            for (DafnyTree child: children) {
                List<String> accept = child.accept(new CallDafnyTreeVisitor(), null);
                methodDeclaration.append(accept);
                methodDeclaration.append(" ");
            }
        }

        return methodDeclaration.toString();
    }

    @Override
    public String visit(DafnyField fi, Void arg) {
        return "Field " + fi.getType().getText() + " " + fi.getName();
    }

    @Override
    public String visit(DafnyFile file, Void arg) {
        return "File " + file.getName();
    }


}