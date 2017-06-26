package edu.kit.iti.algover.overview;

import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeTableCell;
import javafx.scene.control.TreeTableRow;
import javafx.scene.paint.Color;

/**
 * Created by philipp on 26.06.17.
 */
public class NameCell extends TreeTableCell<TreeTableEntity, String> {

    public NameCell() {
        getStyleClass().add("namecell");
    }

    public TreeTableEntity getModel() {
        TreeTableRow<TreeTableEntity> treeTableRow = getTreeTableRow();
        if (treeTableRow == null) return null;
        TreeItem<TreeTableEntity> treeItem = treeTableRow.getTreeItem();
        if (treeItem == null) return null;
        return treeItem.getValue();
    }

    @Override
    protected void updateItem(String item, boolean empty) {
        super.updateItem(item, empty);
        TreeTableEntity model = getModel();
        if (item != null && !empty && model != null) {
            setGraphic(graphicForKind(model.getKind()));
            setText(model.getName());
        }
    }

    private Node graphicForKind(TreeTableEntity.Kind kind) {
        switch (kind) {
            case FUNCTION: return blueLabel("function");
            case CLASS: return blueLabel("class");
            case MODULE: return blueLabel("module");
            case METHOD: return blueLabel("method");
            default: return null;
        }
    }

    private Node blueLabel(String text) {
        Label label = new Label(text);
        label.setTextFill(Color.BLUE);
        return label;
    }
}
