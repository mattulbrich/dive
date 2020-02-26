package edu.kit.iti.algover.timeline;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import javafx.geometry.Side;
import javafx.scene.control.Button;

public class SideArrowButton extends Button {

    public SideArrowButton(Side side) {
        if (side == Side.LEFT) {
            setGraphic(FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.CARET_LEFT, "100px"));
        } else if (side == Side.RIGHT) {
            setGraphic(FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.CARET_RIGHT, "100px"));
        }
        getStyleClass().add("button-overlay");
    }
}
