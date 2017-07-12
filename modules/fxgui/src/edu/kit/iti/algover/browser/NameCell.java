package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntityVisitor;
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
            setGraphic(item.accept(TreeTableEntityRenderer.INSTANCE));
            setText(item.getText());
        } else {
            setGraphic(null);
            setText(null);
        }
    }
}
