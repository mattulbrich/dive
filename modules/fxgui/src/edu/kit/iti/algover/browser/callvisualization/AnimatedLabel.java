package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.control.Label;
import javafx.scene.input.MouseEvent;

/**
 * Component that already has an EventHandler registered that handles the animation
 * for the affordance that the label is clickable
 */
public class AnimatedLabel extends Label {

    private AnimatedLabelMouseEventHandler eventHandler;

    public AnimatedLabel() {
        super();
        eventHandler = new AnimatedLabelMouseEventHandler(this);
        addEventHandler(MouseEvent.MOUSE_ENTERED, eventHandler);
        addEventHandler(MouseEvent.MOUSE_EXITED, eventHandler);
    }

    public AnimatedLabel(String text) {
        super(text);
        eventHandler = new AnimatedLabelMouseEventHandler(this);
        addEventHandler(MouseEvent.MOUSE_ENTERED, eventHandler);
        addEventHandler(MouseEvent.MOUSE_EXITED, eventHandler);
    }

    public AnimatedLabel(String name, DafnyTree dafnyTree, HighlightingHandler listener) {
        super(name);
        eventHandler = new AnimatedLabelMouseEventHandler(this, dafnyTree, listener);
        addEventHandler(MouseEvent.MOUSE_ENTERED, eventHandler);
        addEventHandler(MouseEvent.MOUSE_EXITED, eventHandler);
        addEventHandler(MouseEvent.MOUSE_CLICKED, eventHandler);

    }
}
