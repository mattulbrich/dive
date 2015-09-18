package edu.kit.iti.algover.ui.gui;/**
 * Created by sarah on 8/12/15.
 */

import edu.kit.iti.algover.ui.controller.EntranceViewController;
import edu.kit.iti.algover.ui.util.FileUtilities;
import edu.kit.iti.algover.ui.util.ConfirmBox;
import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

import java.io.IOException;


public class Gui extends Application {

    public static void main(String[] args) {
        launch(args);
    }

    Stage window;
    Scene scene1, scene2;

    @Override
    public void start(Stage primaryStage) {


        this.window = primaryStage;


        //create EntranceView
        FXMLLoader loader = new FXMLLoader(getClass().getResource("EntranceView.fxml"));
        try {
            Parent root = loader.load();
        } catch (IOException e) {
            e.printStackTrace();
        }

        EntranceViewController eView = (EntranceViewController) loader.getController();
        eView.setStage(primaryStage);


        window.setScene(eView.getScene());

        window.setTitle("Intro Screen");
        window.setOnCloseRequest(e ->{
            e.consume();
            Boolean answer = ConfirmBox.display("Closing", "Are you sure you want to close the application?");
            if(answer){
                closeProgram();
            }
        });
        window.show();


    }

    private void closeProgram(){
        System.out.println("Saved");
        window.close();
    }



}
