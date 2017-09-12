package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.geometry.Pos;
import javafx.scene.control.TreeTableCell;

/**
 * Created by Philipp on 14.08.2017.
 */
public class StatusCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    private final PVCClickEditListener engagedListener;

    public StatusCell(PVCClickEditListener engagedListener) {
        this.engagedListener = engagedListener;
        getStyleClass().add("status-cell");
        setAlignment(Pos.CENTER);
    }

    @Override
    protected void updateItem(TreeTableEntity item, boolean empty) {
        super.updateItem(item, empty);
        setText(null);
        if (item != null && !empty) {
            TreeTableEntityStatusRenderer renderer = new TreeTableEntityStatusRenderer(this);
            renderer.applyRendering(item, engagedListener);
        } else {
            setGraphic(null);
            setTooltip(null);
        }
    }

}
