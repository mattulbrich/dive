package edu.kit.iti.algover.ui;/**
 * Created by sarah on 8/12/15.
 */

import javafx.application.Application;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

import java.io.IOException;

public class Gui extends Application {
//fx:controller="edu.kit.iti.algover.ui.AlgoVerifGuiController"
    public static void main(String[] args) {
        launch(args);
    }

    @Override
    public void start(Stage primaryStage) {
        Parent root = null;
        try {
            root = FXMLLoader.load(getClass().getResource("Fluid.fxml"));

        Scene scene = new Scene(root);

        primaryStage.setScene(scene);
        primaryStage.show();

        } catch (IOException e) {
            e.printStackTrace();
        }

    }
//        try {
//            FXMLLoader loader = new FXMLLoader(getClass().getResource("AlgoVer.fxml"));
//            Parent root = (Parent)loader.load();
//
//            //Parent root = FXMLLoader.load(getClass().getResource("AlgoVer.fxml"));
//
//            Scene scene = new Scene(root, 900, 600);
//            ((AlgoVerifGuiController) loader.getController()).setStage(primaryStage);
//            primaryStage.setTitle("Welcome");
//            primaryStage.setScene(scene);
//            primaryStage.show();
//
//        } catch (IOException e) {
//            System.out.println("Cannot load GUI FXML");
//
//        }
//    }
}
