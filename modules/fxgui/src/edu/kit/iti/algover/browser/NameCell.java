package edu.kit.iti.algover.browser;

import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TreeTableCell;
import javafx.scene.paint.Color;

/**
 * Created by philipp on 26.06.17.
 */
public class NameCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    public NameCell() {
        getStyleClass().add("namecell");
    }

    @Override
    protected void updateItem(TreeTableEntity item, boolean empty) {
        super.updateItem(item, empty);
        if (item != null && !empty) {
            setGraphic(graphicForKind(item.getKind()));
            setText(item.getName());
        } else {
            setGraphic(null);
            setText(null);
        }
    }

    private Node graphicForKind(TreeTableEntity.Kind kind) {
        switch (kind) {
            case FUNCTION:
                return blueLabel("function");
            case CLASS:
                return blueLabel("class");
            case MODULE:
                return blueLabel("module");
            case METHOD:
                return blueLabel("method");
            default:
                return null;
        }
    }

    private Node blueLabel(String text) {
        Label label = new Label(text);
        label.setTextFill(Color.BLUE);
        return label;
    }
}
