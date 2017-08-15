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
public class StatusCell extends TreeTableCell<TreeTableEntity, TreeTableEntity.ProofStatus> {

    private final TreeTableEntityEngagedListener engagedListener;

    public StatusCell(TreeTableEntityEngagedListener engagedListener) {
        this.engagedListener = engagedListener;
        getStyleClass().add("status-cell");
    }

    @Override
    protected void updateItem(TreeTableEntity.ProofStatus item, boolean empty) {
        super.updateItem(item, empty);
        setText(null);
        if (item != null && !empty) {
            Text icon = GlyphsDude.createIcon(item.getIcon());
            icon.setFill(item.getFill());
            Label label = new Label(null, icon);
            label.setAlignment(Pos.CENTER);
            label.setTooltip(new Tooltip(item.getTooltip()));
            setGraphic(label);
        } else {
            setGraphic(null);
        }
    }

}
