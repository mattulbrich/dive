package edu.kit.iti.algover.timeline;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import javafx.scene.control.Button;

/**
 * Created by Philipp on 17.08.2017.
 */
public class GoRightArrow extends Button {
    public GoRightArrow(TimelineLayout timelineLayout) {
        setGraphic(FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.CARET_RIGHT, "100px"));
        setOnAction(event -> timelineLayout.moveFrameRight());
        getStyleClass().add("button-overlay");
    }
}
