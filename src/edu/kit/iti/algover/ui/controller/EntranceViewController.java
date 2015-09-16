package edu.kit.iti.algover.ui.controller;


import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.ui.gui.Editor;
import edu.kit.iti.algover.ui.model.ProblemLoader;
import edu.kit.iti.algover.ui.util.FileUtilities;
import javafx.application.Application;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Stage;
import javafx.util.Pair;


import java.io.*;
import java.util.*;

/**
 * Created by sarah on 9/8/15.
 */
public class EntranceViewController extends Application
{
    Stage window;
    Scene scene1;
    String srcCode;
    Button buttonSave = new Button("Save");
    Button buttonLoad = new Button("Load");
    Button buttonReload = new Button("Reload last opened file");
    Button buttonGeneratePO = new Button("Generate Proof Obligations");
    Label poLabel = new Label("Proof Obligations:");
    String name = "";
    Label fileName = new Label(name);
    ListView<String> poList = new ListView();

    File loaded = null;



    Editor editor = new Editor();
    public EntranceViewController(Stage window){
        this.window = window;
        try {
            start(window);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    @Override
    public void start(Stage primaryStage) throws Exception {

        createEntranceView();

    }
    //View which has to be refactored afterwards


    public void createEntranceView() {
        //GridPane mainPane = new GridPane();

        BorderPane mainPane = new BorderPane();
        //Label test= new Label("Test");
        //mainPane.setTop(test);

        buttonLoad.setOnAction(e -> {
            Pair<File, String> p = FileUtilities.fileOpenAction(window);
            srcCode = p.getValue();
            buttonGeneratePO.setDisable(false);
            loaded = p.getKey();
            name = loaded.getAbsolutePath().toString();
            fileName.setText(name);

            editor.replaceText(0, editor.getLength(), srcCode);
        });

        buttonSave.setOnAction(e -> {
            String content = editor.getText();
            FileUtilities.fileSaveAction(window, content);
        });

        buttonReload.setOnAction(e -> {
            //
        });

        buttonGeneratePO.setOnAction(e -> {
            //load the file and parse


            ObservableList<String> items = FXCollections.emptyObservableList();
            LinkedList<String> allObligations = new LinkedList<String>();

            try {

                poList.getItems().clear();
                System.out.println("Cleared\n\n\n");
                ProblemLoader.parse(new BufferedReader(new StringReader(editor.getText())));
                if (loaded != null) {

                   // poList.getItems().clear();
                    for (DafnyTree po : ProblemLoader.getTest()){
                        allObligations.add(po.toStringTree());
                    }
                    if(poList.getItems().size() > 0){
                        System.out.println("Nothing Changed");
                    }else {
                        poList.getItems().clear();
                        items = FXCollections.observableList(allObligations);
                    }
                } else {
                items.add("Failed");
                 }
                 } catch (Exception e1) {
                    e1.printStackTrace();
                }
            poList.setItems(items);

        });

        editor.textProperty().addListener(new ChangeListener<String>() {
            @Override
            public void changed(ObservableValue<? extends String> observable, String oldValue, String newValue) {
                System.out.println(newValue);
            }

        });

//        sourceCode.textProperty().addListener(new ChangeListener<String>() {
//            @Override
//            public void changed(ObservableValue<? extends String> observable, String oldValue, String newValue) {
//                System.out.println("old: "+oldValue);
//                System.out.println("new: "+newValue);
//            }
//        });

            //sourceCode.getText();
            BorderPane poPane = new BorderPane();
            poPane.setTop(poLabel);
            poPane.setCenter(poList);

            VBox vb = new VBox();
            buttonGeneratePO.setDisable(true);
            vb.getChildren().addAll(poPane, buttonGeneratePO);

            HBox hb = new HBox();
            hb.getChildren().addAll(buttonSave, buttonLoad, buttonReload, fileName);
            mainPane.setTop(hb);
            mainPane.setCenter(editor);
            mainPane.setRight(vb);

            scene1 = new Scene(mainPane, 1024, 678);
        }

    public Scene getScene(){
        return scene1;
    }

}
