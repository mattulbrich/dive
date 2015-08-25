package edu.kit.iti.algover.ui.gui;/**
 * Created by sarah on 8/12/15.
 */

import edu.kit.iti.algover.ui.controller.ProgrammeViewController;
import edu.kit.iti.algover.ui.util.ConfirmBox;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

public class Gui extends Application {
//fx:controller="edu.kit.iti.algover.ui.controller.AlgoVerifGuiController"
    public static void main(String[] args) {
        launch(args);
    }

    Stage window;
    Scene scene1, scene2;

    @Override
    public void start(Stage primaryStage) {
        this.window = primaryStage;

        TopMenu tm = new TopMenu(primaryStage);
        Label label = new Label("Welcome to AlgoVerif. Please Choose your preferred view.");
        //Button loadFile = new Button("Load File...");
        //button1.setOnAction(e -> window.setScene(scene2));
//        loadFile.setOnAction(e -> {
//            Boolean answer = ConfirmBox.display("Closing", "Are you sure you want to close the application?");
//            if(answer){
//                closeProgram();
//            }
//        });

        BorderPane mainLayout = new BorderPane();
        mainLayout.setCenter(label);
     //   mainLayout.setBottom(loadFile);
        mainLayout.setTop(tm);
        //layout1.getChildren().setAll(label, button1);
        scene1 = new Scene(mainLayout, 1024, 678);

        /*Label label1 = new Label("Welcome to Scene2");
        Button button2 = new Button("ToScene2");
        button2.setOnAction(e -> window.setScene(scene1));
        StackPane layout2 = new StackPane();
        layout2.getChildren().setAll(label1, button2);
        scene2 = new Scene(layout2, 600,600);*/

        window.setScene(scene1);
        window.setTitle("Intro Screen");
        window.setOnCloseRequest(e ->{
            e.consume();
            Boolean answer = ConfirmBox.display("Closing", "Are you sure you want to close the application?");
            if(answer){
                closeProgram();
            }
        });
        window.show();

        /*Parent root = null;
        try {
            root = FXMLLoader.load(getClass().getResource("Fluid.fxml"));

        Scene scene = new Scene(root);

        primaryStage.setScene(scene);
        primaryStage.show();

        } catch (IOException e) {
            e.printStackTrace();
        }*/

    }

    private void closeProgram(){
        System.out.println("Saved");
        window.close();
    }
/*        try {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("AlgoVer.fxml"));
            Parent root = (Parent)loader.load();

            //Parent root = FXMLLoader.load(getClass().getResource("AlgoVer.fxml"));

            Scene scene = new Scene(root, 900, 600);
            ((AlgoVerifGuiController) loader.getController()).setStage(primaryStage);
            primaryStage.setTitle("Welcome");
            primaryStage.setScene(scene);
            primaryStage.show();

        } catch (IOException e) {
            System.out.println("Cannot load GUI FXML");

        }
    }*/
}
