package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.parser.DafnyTree;
import javafx.event.EventHandler;
import javafx.event.EventType;
import javafx.scene.control.Label;
import javafx.scene.input.MouseEvent;
import org.antlr.runtime.Token;


public class AnimatedLabelMouseEventHandler implements EventHandler<MouseEvent> {

    private final Label l;

    private String filename = "";

    private Token start = null;

    private Token end = null;

    private HighlightingHandler listener = null;



    public AnimatedLabelMouseEventHandler(Label l, String filename, Token start, Token end, HighlightingHandler listener) {
        this.l = l;
        this.filename = filename;
        this.start = start;
        this.end = end;
        this.listener = listener;
    }

    public AnimatedLabelMouseEventHandler(Label l, DafnyTree entity, HighlightingHandler listener) {
        this.l = l;
        this.filename = entity.getFilename();
        this.start = entity.getStartToken();
        this.end = entity.getStopToken();
        this.listener = listener;
    }


    public AnimatedLabelMouseEventHandler(Label l) {
        this.l = l;
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
        if(eventType == MouseEvent.MOUSE_CLICKED){
            handleMouseClick();
        }

    }

    private void handleMouseClick() {
        if(listener != null){
            listener.onRequestHighlight(filename, start, end);
        }
    }

    private void handleMouseEntry(){
        l.setBackground(AbstractCallEntity.SELECTED_LABEL);
        l.setScaleX(1.2);
        l.setScaleY(1.2);
        if(listener != null){
            listener.onRequestHighlight(filename, start, end);
        }


    }
    private void handleMouseExit(){
        l.setBackground(AbstractCallEntity.WHITE_BACKGROUND);
        l.setScaleX(1);
        l.setScaleY(1);

    }

    public Label getLabel() {
        return l;
    }



    public String getFilename() {
        return filename;
    }

    public void setFilename(String filename) {
        this.filename = filename;
    }

    public Token getStart() {
        return start;
    }

    public void setStart(Token start) {
        this.start = start;
    }

    public Token getEnd() {
        return end;
    }

    public void setEnd(Token end) {
        this.end = end;
    }

    public HighlightingHandler getListener() {
        return listener;
    }

    public void setListener(HighlightingHandler listener) {
        this.listener = listener;
    }
}
