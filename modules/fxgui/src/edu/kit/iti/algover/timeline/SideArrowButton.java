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
 *
 * @author Valentin
 */
public class SideArrowButton extends Button {

    /**
     * Icon of button.
     */
    private Node icon;

    /**
     * This stores the preferred width of this {@link Button}
     * in the scene.
     */
    private final double assignedPrefWidth;

    /**
     * Create a new {@link Button} for a side with icon.
     * Currently supported {@link Side#LEFT} and {@link Side#RIGHT}
     * @param side
     *          {@link Side} which this buttin should indicate.
     */
    public SideArrowButton(Side side) {
        this.icon = null;
        if (side == Side.LEFT) {
            this.icon =
                    FontAwesomeIconFactory.get().
                            createIcon(FontAwesomeIcon.CARET_LEFT, "100px");
        } else if (side == Side.RIGHT) {
            this.icon =
                    FontAwesomeIconFactory.get().
                            createIcon(FontAwesomeIcon.CARET_RIGHT, "100px");
        }
        setGraphic(this.icon);
        getStyleClass().add("button-overlay");
        this.assignedPrefWidth = this.getPrefWidth();
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
        setGraphic(this.icon);
        setPrefWidth(this.assignedPrefWidth);
    }
}
