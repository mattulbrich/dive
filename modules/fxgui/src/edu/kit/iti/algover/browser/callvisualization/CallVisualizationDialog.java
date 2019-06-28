package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.Lookup;
import javafx.scene.control.*;
import org.antlr.runtime.Token;

public class CallVisualizationDialog extends Alert implements HighlightingHandler{


    private DialogPane pane;

    //needs to build model and pass reference for selection model

    public CallVisualizationDialog(CallVisualizationModel model, Lookup lookup){
        super(AlertType.INFORMATION);

        pane = new SimpleListVisualizationPane(model, this);
        this.setDialogPane(pane);
        this.getButtonTypes().add(ButtonType.CLOSE);
    }


    @Override
    public void onRequestHighlight(String filename, Token startToken, Token stopToken) {
        System.out.println("t = " + startToken);
    }
}
