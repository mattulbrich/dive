package edu.kit.iti.algover.ui.util;

import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

import javax.swing.*;

/**
 * Created by sarah on 8/20/15.
 */
public class AlertBox {
    /**
     * Tutorial:
     * @param title
     * @param msg to display to the user
     */
    public static void display(String title, String msg){
        Stage window = new Stage();

        //Block all input Events until this window is done
        window.initModality(Modality.APPLICATION_MODAL);
        window.setTitle(title);
        window.setMaxWidth(350);
        Label l = new Label(msg);
        Button buttonClose = new Button("Close");
        buttonClose.setOnAction(e -> window.close());

        HBox layout = new HBox();
        layout.getChildren().addAll(l, buttonClose);
        layout.setAlignment(Pos.CENTER);

        Scene scene = new Scene(layout);
        window.setScene(scene);
        //Show Stage until closed
        window.showAndWait();
    }
}
