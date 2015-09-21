package edu.kit.iti.algover.ui.controller;


import edu.kit.iti.algover.Proof;
import edu.kit.iti.algover.ProofCenter;
import edu.kit.iti.algover.ui.gui.Editor;
import edu.kit.iti.algover.ui.gui.Gui;
import edu.kit.iti.algover.ui.model.ProblemLoader;
import edu.kit.iti.algover.ui.util.AlertBox;
import edu.kit.iti.algover.ui.util.FileUtilities;
import javafx.application.Application;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.TextArea;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import javafx.util.Pair;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.LinkedList;
import java.util.prefs.Preferences;

/**
 * Created by sarah on 9/8/15.
 */
public class POViewController extends Application
{
    Stage window;
    Scene scene1;
    String srcCode;
    @FXML
    Button buttonSave;
    @FXML
    Button buttonLoad;
    @FXML
    Button buttonReload;
//    @FXML
//    Label poLabel = new Label("Proof Obligations:");
    String name = "";
    @FXML
    Label fileName;

    @FXML
    TextArea assumptionsField;

    @FXML
    TextArea toShowField;

    File loaded = null;
    @FXML
    Editor editor;

    @FXML
    VBox main;


    @Override
    public void start(Stage primaryStage) throws Exception {
        createEntranceView();
    }


    public void setStage(Stage s) { this.window = s;
            try {
            start(window);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    public void createEntranceView() {
            //set actions
            buttonLoad.setOnAction(e -> loadAction());
            buttonSave.setOnAction(e -> {
                String content = editor.getText();
                FileUtilities.fileSaveAction(window, content);
            });
            buttonReload.setOnAction(e -> reloadAction());

            editor.textProperty().addListener(new ChangeListener<String>() {
                @Override
                public void changed(ObservableValue<? extends String> observable, String oldValue, String newValue) {
                    // System.out.println(newValue);
                    //TODO search generated POs if they should be generated again
                }

            });

            scene1 = new Scene(main, 1024, 678);
        }

    public Scene getScene(){
        return scene1;
    }

    public void loadAction(){
        Pair<File, String> p = FileUtilities.fileOpenAction(window);
        srcCode = p.getValue();

        loaded = p.getKey();
        name = loaded.getAbsolutePath().toString();
        fileName.setText(name);

        editor.replaceText(0, editor.getLength(), srcCode);
        setLastFile(loaded);
    }

    /**
     * Reload last opened file TODO
     */
    public void reloadAction(){
        Preferences prefs = Preferences.userNodeForPackage(Gui.class);
        String filePath = prefs.get("filePath" , null);
           if (filePath != null) {
              BufferedReader re = FileUtilities.readFile(new File(filePath));
               try {
                   editor.replaceText(0,editor.getLength(), re.readLine());
               } catch (IOException e) {
                   e.printStackTrace();
               }
               //return new File(filePath);
    } else {
               System.out.println("File not loadable");
        //return null;
    }

    }

    public void setLastFile(File file) {
        Preferences prefs = Preferences.userNodeForPackage(Gui.class);
        if (file != null) {
            prefs.put("filePath", file.getPath());

        } else {
            prefs.remove("filePath");
        }
    }


}
