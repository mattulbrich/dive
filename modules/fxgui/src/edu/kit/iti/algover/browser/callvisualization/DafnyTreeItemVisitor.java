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
    public TreeItem<DafnyTree> visitDECREASES(DafnyTree t, TreeItem<DafnyTree> dafnyTreeTreeItem) {
        TreeItem<DafnyTree> newItem = new TreeItem<>(t);
        dafnyTreeTreeItem.getChildren().add(newItem);
        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, newItem));
        return dafnyTreeTreeItem;
    }

    @Override
    public TreeItem<DafnyTree> visitDefault(DafnyTree t, TreeItem<DafnyTree> parent) {
        TreeItem<DafnyTree> newItem = new TreeItem<>(t);
        parent.getChildren().add(newItem);
        t.getChildren().forEach(dafnyTree -> dafnyTree.accept(this, newItem));
        return parent;

    }

    @Override
    public TreeItem<DafnyTree> visitBLOCK(DafnyTree t, TreeItem<DafnyTree> dafnyTreeTreeItem) {
        return null;
    }

    @Override
    public TreeItem<DafnyTree> visitBLOCK_BEGIN(DafnyTree t, TreeItem<DafnyTree> dafnyTreeTreeItem) {
        return null;
    }

    @Override
    public TreeItem<DafnyTree> visitBLOCK_END(DafnyTree t, TreeItem<DafnyTree> dafnyTreeTreeItem) {
        return null;
    }


}
