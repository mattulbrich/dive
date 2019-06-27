package edu.kit.iti.algover.browser.callvisualization;

import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.layout.VBox;



public class CallPane extends VBox {

    private final AbstractCallEntity entity;

    private final String category;

    private Label header;

    private ListView<Label> precondition;

    private ListView<Label> postcondition;


    public CallPane(AbstractCallEntity entity){
        this.entity = entity;
        if(entity.isCall()){
            category = "Calls";
        } else {
            category = "Called by";
        }
        getChildren().add(new Label(category+ " " +entity.getEntityName()+ " in line "+entity.getUsageLine()));
        fillPane();
    }

    private void fillPane() {
        header = new Label(entity.getEntityName());
        header.setOnMouseClicked(event -> {
            System.out.println(entity.getEntity());
        });
        this.getChildren().add(header);

    }


}
