package edu.kit.iti.algover.browser;

import de.jensd.fx.glyphs.GlyphsDude;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.control.TreeTableCell;
import javafx.scene.text.Text;

/**
 * Created by Philipp on 14.08.2017.
 */
public class StatusCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    private final TreeTableEntityEngagedListener engagedListener;

    public StatusCell(TreeTableEntityEngagedListener engagedListener) {
        this.engagedListener = engagedListener;
        getStyleClass().add("status-cell");
        setAlignment(Pos.CENTER);
    }

    @Override
    protected void updateItem(TreeTableEntity item, boolean empty) {
        super.updateItem(item, empty);
        setText(null);
        if (item != null && !empty) {
            setGraphic(item.accept(TreeTableEntityStatusRenderer.INSTANCE));
        } else {
            setGraphic(null);
            setTooltip(null);
        }
    }

}
