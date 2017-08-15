package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.scene.control.TreeTableCell;
import javafx.scene.input.MouseEvent;

/**
 * Created by philipp on 26.06.17.
 */
public class NameCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    private final TreeTableEntityEngagedListener engagedListener;

    public NameCell(TreeTableEntityEngagedListener engagedListener) {
        this.engagedListener = engagedListener;
        getStyleClass().add("namecell");
        addEventFilter(MouseEvent.MOUSE_CLICKED, this::onMouseClick);
    }

    private void onMouseClick(MouseEvent event) {
        if (event.getClickCount() == 2 && engagedListener != null && getItem() != null) {
            engagedListener.onDoubleClickTreeEntity(getItem());
        }
    }

    @Override
    protected void updateItem(TreeTableEntity item, boolean empty) {
        super.updateItem(item, empty);
        if (item != null && !empty) {
            setGraphic(item.accept(TreeTableEntityNameRenderer.INSTANCE));
            setText(item.getText());
        } else {
            setGraphic(null);
            setText(null);
        }
    }
}
