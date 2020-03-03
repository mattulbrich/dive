/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.timeline;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.control.Button;

/**
 * Created by Valentin on 25.02.20
 */
public class SideArrowButton extends Button {

    private Node graphic;
    private final double prefWidth;

    public SideArrowButton(Side side) {
        this.graphic = null;
        if (side == Side.LEFT) {
            this.graphic =
                    FontAwesomeIconFactory.get().
                            createIcon(FontAwesomeIcon.CARET_LEFT, "100px");
        } else if (side == Side.RIGHT) {
            this.graphic =
                    FontAwesomeIconFactory.get().
                            createIcon(FontAwesomeIcon.CARET_RIGHT, "100px");
        }
        setGraphic(this.graphic);
        getStyleClass().add("button-overlay");
        this.prefWidth = this.getPrefWidth();
    }

    /**
     * Hide the button without removing it from parent.
     * Disable it and set width to zero.
     */
    public void hide() {
        setDisable(true);
        setGraphic(null);
        setPrefWidth(0);
    }

    /**
     * Show button.
     * Enable it and set width to a the attribute specified value.
     */
    public void show() {
        setDisable(false);
        setGraphic(this.graphic);
        setPrefWidth(this.prefWidth);
    }
}
