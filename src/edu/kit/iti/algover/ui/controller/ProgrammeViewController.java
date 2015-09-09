package edu.kit.iti.algover.ui.controller;

import edu.kit.iti.algover.ui.util.FileUtilities;
import edu.kit.iti.algover.ui.util.ConfirmBox;
import javafx.application.Application;
import javafx.geometry.Side;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;
import org.controlsfx.control.HiddenSidesPane;
import org.controlsfx.control.MasterDetailPane;

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
            String source = openFile(primaryStage);
            srcPane.setText(source);
        });

        //options..
        Menu optionsMenu = new Menu("Options");
        Menu aboutMenu = new Menu("About");
        Menu menuView = new Menu("View");

        //add to menu
        topMenu.getMenus().addAll(fileMenu, optionsMenu, menuView, aboutMenu);



        srcPane= new TextArea("");
        MasterDetailPane masterPane = new MasterDetailPane();

        HiddenSidesPane mainPane = new HiddenSidesPane();


        BorderPane mainLayout = new BorderPane();

        mainLayout.setCenter(srcPane);

        mainPane.setContent(mainLayout);

        mainPane.setTop(topMenu);
        masterPane.setMasterNode(mainPane);

        masterPane.setDetailSide(Side.LEFT);
        masterPane.setShowDetailNode(true);
        masterPane.setAnimated(true);
        scene = new Scene(masterPane, 1024, 678);
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

    private static String  openFile(Stage stage){
        String source= FileUtilities.fileOpenAction(stage).getValue();
        return source;
       // srcPane.setText(source);
  }
   public void setStage(Stage stage){
        this.window = stage;
    }

}
