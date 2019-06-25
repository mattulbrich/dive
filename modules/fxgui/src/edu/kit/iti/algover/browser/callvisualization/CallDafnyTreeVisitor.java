package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;

import java.util.ArrayList;
import java.util.List;

public class CallDafnyTreeVisitor extends DafnyTreeDefaultVisitor<List<String>, Void> {


    @Override
    public List<String> visitDefault(DafnyTree t, Void a) {
        List<String> list = new ArrayList<>();
        list.add(t.getText());
        if(t.getChildren() != null) {
            t.getChildren().forEach(dafnyTree -> {
                list.addAll(dafnyTree.accept(this, a));
            });
        }
        return list;

    }

    @Override
    public List<String> visitTYPE(DafnyTree t, Void aVoid) {
        List<DafnyTree> children = t.getChildren();
        assert children.size()==1;
        return t.getChild(0).accept(this, aVoid);
    }
}