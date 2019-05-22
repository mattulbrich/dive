package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.control.*;

import java.util.Collection;


public class CallVisualizationDialog extends Alert {


    private DialogPane pane;

    //needs to build model and pass reference for selection model

    public CallVisualizationDialog(Collection<DafnyTree> callList, DafnyDecl selectedDecl){
        super(AlertType.INFORMATION);
        pane = new SimpleListVisualizationPane(callList,selectedDecl);
        this.setDialogPane(pane);
        this.getButtonTypes().add(ButtonType.CLOSE);
        CallVisualizationModel model = new CallVisualizationModel();
    }




}
