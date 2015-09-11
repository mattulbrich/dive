package edu.kit.iti.algover.ui.controller;

import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.ui.model.ProblemLoader;
import edu.kit.iti.algover.ui.util.ConfirmBox;
import edu.kit.iti.algover.ui.util.FileUtilities;
import javafx.application.Application;
import javafx.beans.InvalidationListener;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.stage.Stage;
import javafx.util.Pair;

import org.controlsfx.control.ListSelectionView;

import javax.swing.text.StyledEditorKit;

import java.io.File;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

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

    TextArea sourceCode = new TextArea();
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
            sourceCode.setText(srcCode);
            buttonGeneratePO.setDisable(false);

            loaded = p.getKey();
            name = loaded.getAbsolutePath().toString();
            fileName.setText(name);
        });

        buttonSave.setOnAction(e -> {
            String content = sourceCode.getText();
            FileUtilities.fileSaveAction(window, content);
        });

        buttonReload.setOnAction(e -> {
            //
        });

        buttonGeneratePO.setOnAction(e -> {
            //load the file and parse
            poList.getItems().clear();
            ObservableList<String> items = FXCollections.emptyObservableList();
            ProblemLoader.readFile(loaded);
            //ProblemLoader.results;
            if (loaded != null) {
                items = FXCollections.observableList(ProblemLoader.getPos());
            } else {
                items.add("Failed");
            }
            poList.setItems(items);
            System.out.println("Parse the File");
        });

        sourceCode.setOnInputMethodTextChanged(e -> {

        });
        BorderPane poPane = new BorderPane();
        poPane.setTop(poLabel);
        poPane.setCenter(poList);

        VBox vb = new VBox();
        buttonGeneratePO.setDisable(true);
        vb.getChildren().addAll(poPane, buttonGeneratePO);

        HBox hb = new HBox();
        hb.getChildren().addAll(buttonSave, buttonLoad, buttonReload, fileName);
    //TODO: line numbers are missing
        sourceCode.setText(srcCode);
        ScrollPane sp = new ScrollPane();
        sp.setFitToHeight(true);
        sp.setContent(sourceCode);
        mainPane.setTop(hb);
        mainPane.setCenter(sp);
        mainPane.setRight(vb);
        //HBox pos = new HBox();
        //pos.setSpacing(10);
        //pos.getChildren().addAll(test);
        //mainPane.getChildren().addAll(sp, pos);   // Add grid from Example 1-5
        //mainPane.setBottomAnchor(pos, 8.0);
        //mainPane.setRightAnchor(pos, 5.0);
        //mainPane.setTopAnchor(sp, 50.0);
        scene1 = new Scene(mainPane, 1024, 678);
    }

    public Scene getScene(){
        return scene1;
    }

}
