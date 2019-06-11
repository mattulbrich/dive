package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class DafnyTreeCallEntityVisitor extends DafnyTreeDefaultVisitor<Collection<String>, List<String>> {

    @Override
    public Collection<String> visitFUNCTION(DafnyTree t, List<String> collections) {

        collections.add("function "+t.getChild(0).getText());
        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, collections));
        return null;

    }

    @Override
    public Collection<String> visitDefault(DafnyTree t, List<String> arg) {
        arg.add(t.getText());
        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, arg));
        return null;


    }
}
