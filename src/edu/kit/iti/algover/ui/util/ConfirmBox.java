package edu.kit.iti.algover.ui.util;

import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.stage.Modality;
import javafx.stage.Stage;

/**
 * Created by sarah on 8/20/15.
 */
public class ConfirmBox{
    static Boolean answer;
      /**
     * Tutorial:
     * @param title
     * @param msg to display to the user
     */
    public static boolean display(String title, String msg){
        Stage window = new Stage();

        //Block all input Events until this window is done
        window.initModality(Modality.APPLICATION_MODAL);
        window.setTitle(title);
        window.setMaxWidth(400);
        Label l = new Label(msg);
        l.setPadding(new Insets(10,10,10,10));

        Button confirm = new Button("Yes");
        Button decline = new Button("No");

        confirm.setOnAction(e -> {
            answer = true;
            window.close();
        });
        decline.setOnAction(e -> {
            answer = false;
            window.close();
        });
        BorderPane mainLayout = new BorderPane();


        HBox buttonLayout = new HBox();
        buttonLayout.setAlignment(Pos.CENTER);
        buttonLayout.getChildren().add(confirm);
        buttonLayout.setSpacing(20);
        buttonLayout.getChildren().add(decline);

        mainLayout.setCenter(l);
        mainLayout.setBottom(buttonLayout);

        mainLayout.setPadding(new Insets(10, 10, 10, 10));
        Scene scene = new Scene(mainLayout);
        window.setScene(scene);
        //Show Stage until closed
        window.showAndWait();
        return answer;
    }
}
