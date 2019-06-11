package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;

import java.util.List;

public class DafnyTreeCallEntityVisitor extends DafnyTreeDefaultVisitor<Void, List<String>> {


    @Override
    public Void visitDefault(DafnyTree t, List<String> arg) {
        arg.add(t.getText());
        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, arg));
        return null;


    }
}
