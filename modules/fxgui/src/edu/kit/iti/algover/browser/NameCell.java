package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntityVisitor;
import javafx.event.Event;
import javafx.event.EventHandler;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TreeTableCell;
import javafx.scene.input.MouseEvent;
import javafx.scene.paint.Color;

/**
 * Created by philipp on 26.06.17.
 */
public class NameCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    private final TreeEntityDoubleClickListener doubleClickListener;

    public NameCell(TreeEntityDoubleClickListener doubleClickListener) {
        this.doubleClickListener = doubleClickListener;
        getStyleClass().add("namecell");
        addEventFilter(MouseEvent.MOUSE_CLICKED, this::onMouseClick);
    }

    // TODO: Make this accessible more visually, i.e. a context menu or better: a button
    private void onMouseClick(MouseEvent event) {
        if (event.getClickCount() == 2 && doubleClickListener != null && getItem() != null) {
            doubleClickListener.onDoubleClickTreeEntity(getItem());
        }
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
