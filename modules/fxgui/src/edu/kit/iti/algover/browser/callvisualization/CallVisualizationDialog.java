package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.Lookup;
import javafx.scene.control.*;

public class CallVisualizationDialog extends Alert {


    private DialogPane pane;

    //needs to build model and pass reference for selection model

    public CallVisualizationDialog(CallVisualizationModel model, Lookup lookup){
        super(AlertType.INFORMATION);

        pane = new SimpleListVisualizationPane(model);
        this.setDialogPane(pane);
        this.getButtonTypes().add(ButtonType.CLOSE);
    }




}
