package edu.kit.iti.algover.browser.callvisualization;

import javafx.event.EventHandler;
import javafx.event.EventType;
import javafx.scene.control.Label;
import javafx.scene.input.MouseEvent;


public class AnimatedLabelMouseEventHandler implements EventHandler<MouseEvent> {

    private Label l;


    public AnimatedLabelMouseEventHandler(Label l) {
        this.l = l;
    }

    public void handleMouseEntry(){
        l.setBackground(AbstractCallEntity.SELECTED_LABEL);
        l.setScaleX(1.2);
        l.setScaleY(1.2);

    }
    public void handleMouseExit(){
        l.setBackground(AbstractCallEntity.WHITE_BACKGROUND);
        l.setScaleX(1);
        l.setScaleY(1);
    }

    @Override
    public void handle(MouseEvent event) {
        EventType<? extends MouseEvent> eventType = event.getEventType();
        if(eventType == MouseEvent.MOUSE_ENTERED){
                handleMouseEntry();
        }
        if(eventType == MouseEvent.MOUSE_EXITED){
            handleMouseExit();
        }

    }
}
