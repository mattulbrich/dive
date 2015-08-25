package edu.kit.iti.algover.ui.controller;

import edu.kit.iti.algover.Main;
import edu.kit.iti.algover.ui.util.ConfirmBox;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

import java.io.*;

/**
 * Created by sarah on 8/20/15.
 */
public class ProgrammeViewController extends Application {
    Scene scene;
    Stage window;
    TextArea srcPane;

    @Override
    public void start(Stage primaryStage) throws Exception {
        window= primaryStage;

        //menu bar
        MenuBar topMenu = new MenuBar();

        //File...
        Menu fileMenu = new Menu("File");
        MenuItem openFile = new MenuItem("Open File ...");
        fileMenu.getItems().add(openFile);
        openFile.setOnAction(e -> {
            openFile(primaryStage);
        });

        //options..
        Menu optionsMenu = new Menu("Options");
        Menu aboutMenu = new Menu("About");
        Menu menuView = new Menu("View");

        //add to menu
        topMenu.getMenus().addAll(fileMenu, optionsMenu, menuView, aboutMenu);

        //Label label = new Label("Welcome to Scene3");
        //Button button1 = new Button("ToScene2");
        //button1.setOnAction(e -> window.setScene(scene2));
//        button1.setOnAction(e -> {
//            Boolean answer = ConfirmBox.display("Closing", "Are you sure you want to close the application?");
//            if(answer){
//                closeProgram();
//            }
//        });

        srcPane= new TextArea("");

        BorderPane mainLayout = new BorderPane();
        mainLayout.setCenter(srcPane);
        //mainLayout.setBottom(button1);
        mainLayout.setTop(topMenu);
        //layout1.getChildren().setAll(label, button1);
        scene = new Scene(mainLayout, 1024, 678);
        window.setScene(scene);
        window.setTitle("Test");
        window.setOnCloseRequest(e -> {
            e.consume();
            Boolean answer = ConfirmBox.display("Closing", "Are you sure you want to close the application?");
            if (answer) {
                closeProgram();
            }
        });
        window.show();

    }

    private void closeProgram(){
        System.out.println("Saved");
        window.close();
    }

    private void openFile(Stage stage){
        FileChooser fileChooser = new FileChooser();
        File file = fileChooser.showOpenDialog(stage);
        Main.readFile(file);
        String text= "";
        String textline="";
        int line= 1;
        BufferedReader br = readFile(file);

        if(br != null) {

            while (textline != null) {
                try {
                    textline=  br.readLine();
                    text += line + ": " + textline + "\n";
                    line++;
                } catch (IOException e) {
                    e.printStackTrace();
                }

            }
            try {
                br.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
            srcPane.setText(text);



        }else {
            srcPane.setText("File not read");
            // Main.readFile(file);
        }
  }
   public void setStage(Stage stage){
        this.window = stage;
    }
    public static BufferedReader readFile(File file) {
        try {
            BufferedReader br = new BufferedReader(new FileReader(file));
            return br;


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            System.out.println("Could not load problem");
        }return null;


    }
}
