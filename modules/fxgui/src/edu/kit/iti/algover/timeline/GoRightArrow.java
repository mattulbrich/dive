package edu.kit.iti.algover.timeline;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import javafx.scene.control.Button;

/**
 * Created by Philipp on 17.08.2017.
 */
public class GoRightArrow extends Button {
    public GoRightArrow(TimelineLayout timelineLayout) {
        setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.CARET_RIGHT, "100px"));
        setOnAction(event -> timelineLayout.moveFrameRight());
        getStyleClass().add("button-overlay");
    }
}
