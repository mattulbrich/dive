package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import javafx.scene.control.TreeItem;

public class DafnyTreeItemVisitor extends DafnyTreeDefaultVisitor<TreeItem<DafnyTree>, TreeItem<DafnyTree>> {
    @Override
    public TreeItem<DafnyTree> visitCALL(DafnyTree t, TreeItem<DafnyTree> dafnyTreeTreeItem) {

        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, dafnyTreeTreeItem));
        return dafnyTreeTreeItem;

    }

    @Override
    public TreeItem<DafnyTree> visitDefault(DafnyTree t, TreeItem<DafnyTree> parent) {
        TreeItem<DafnyTree> newItem = new TreeItem<DafnyTree>(t);
        parent.getChildren().add(newItem);
        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, newItem));
        return parent;
    }
}
