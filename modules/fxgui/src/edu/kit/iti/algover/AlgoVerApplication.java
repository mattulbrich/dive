/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import com.jfoenix.controls.JFXButton;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.DafnyProjectManager;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;
import edu.kit.iti.algover.settings.ProjectSettingsController;
import edu.kit.iti.algover.settings.SettingsFactory;
import edu.kit.iti.algover.util.FormatException;
import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 15.06.2017.
 * Adapted by S.Grebing in March 2019
 */
public class AlgoVerApplication extends Application {

    private Stage primaryStage;

    private Stage substage;


    public static void main(String[] args) {
        launch(args);
    }

    // Used for calculating the syntax highlighting asynchronously
    private static final ExecutorService SYNTAX_HIGHLIGHTING_EXECUTOR = Executors.newSingleThreadExecutor();



    @Override
    public void start(Stage primaryStage) throws Exception {
        this.primaryStage = primaryStage;
        //create Welcome Dialog
        createAndShowWelcomePane(primaryStage);
    }

    private void createAndShowWelcomePane(Stage primaryStage) {
        primaryStage.setTitle("AlgoVer");

        BorderPane pane = new BorderPane();
        pane.setPrefSize(400.0,200.0);
        VBox vbox= new VBox();
        vbox.setSpacing(50);
        vbox.setAlignment(Pos.CENTER);
        HBox buttonBox = new HBox();
        buttonBox.setAlignment(Pos.BASELINE_CENTER);
        buttonBox.setSpacing(50);
        String text = "Welcome to AlgoVer \n A seamless verification system for Dafny programs.\n";
        Label welcomeText = new Label(text);

        //Buttons
        JFXButton openFileChooser = new JFXButton("Open existing project");
        openFileChooser.setButtonType(JFXButton.ButtonType.RAISED);
        openFileChooser.setOnAction(this::handleFileChooserAction);

        JFXButton createProject = new JFXButton("Create new project");
        createProject.setButtonType(JFXButton.ButtonType.RAISED);
        createProject.setOnAction(this::createNewProjectHandler);


        buttonBox.getChildren().addAll(createProject,openFileChooser);
        vbox.getChildren().addAll(welcomeText, buttonBox);
        pane.setCenter(vbox);

        primaryStage.setScene(new Scene(pane));
        primaryStage.setWidth(900);
        primaryStage.setHeight(700);
        primaryStage.show();


    }


    private void createAndShowConfigPane(Stage substage) {
        List<Node> collect = SettingsFactory.getSettingsPanel().stream().filter(node ->
                node.getUserData().equals(ProjectSettingsController.NAME)).collect(Collectors.toList());
        if(!collect.isEmpty()){
            BorderPane configPane = new BorderPane();
            configPane.setPrefSize(600.0, 400.0);
            //configPane.setCenter(collect.get(0));
            configPane.setCenter(new ScrollPane(collect.get(0)));
            //Buttons
            ButtonBar buttonBar = new ButtonBar();
            JFXButton applyConfig = new JFXButton("Create Configuration");
            applyConfig.setButtonType(JFXButton.ButtonType.RAISED);
            ButtonBar.setButtonData(applyConfig, ButtonBar.ButtonData.APPLY);
            applyConfig.setOnAction(this::createConfigurationAndLoadProject);

            JFXButton cancelButton = new JFXButton("Cancel");
            cancelButton.setButtonType(JFXButton.ButtonType.RAISED);
            ButtonBar.setButtonData(cancelButton, ButtonBar.ButtonData.CANCEL_CLOSE);

            buttonBar.getButtons().addAll(applyConfig, cancelButton);
            configPane.setBottom(buttonBar);
            Scene configurationScene = new Scene(configPane);
            substage.setScene(configurationScene);

        } else {
            BorderPane pane = new BorderPane();
            String error = "Could not create configuration creation dialog. Please contact the developers.";
            pane.setCenter(new TextArea(error));
            substage.setScene(new Scene(pane));
        }
    }

    private File constructFileChooser() {
        File projectFile;
        Parameters params = getParameters();
        List<String> fileNames = params.getUnnamed();
        if(fileNames.isEmpty()) {

            FileChooser chooser = new FileChooser();

            chooser.setTitle("Choose project folder");
            chooser.setInitialDirectory(new File("doc/examples/"));
            projectFile = chooser.showOpenDialog(primaryStage);
            ProjectManager manager;
            if (projectFile == null) {
                return null;
            }
        } else {
            projectFile = new File(fileNames.get(0)).getAbsoluteFile();
        }
        return projectFile;

    }


    @Override
    public void stop() throws Exception {
        SYNTAX_HIGHLIGHTING_EXECUTOR.shutdown();
    }

    //region ActionHandler

    public void createNewProjectHandler(ActionEvent event){
        createAndShowConfigPane(primaryStage);

    }

    private void handleFileChooserAction(ActionEvent actionEvent) {
        File projectFile;
        ProjectManager manager;
        try {
            projectFile = constructFileChooser();
            if(projectFile != null) {
                if (projectFile.getName().endsWith(".xml")) {
                    // Read all PVCs and update GUId
                    manager = new XMLProjectManager(projectFile.getParentFile(), projectFile.getName());
                } else if (projectFile.getName().endsWith(".dfy")) {
                    manager = new DafnyProjectManager(projectFile);
                } else {
                    throw new IllegalArgumentException("AlgoVer supports only .dfy and .xml files.");
                }


                // TODO Maybe don't do this initially (might hurt UX, when there are a lot of proofs)
                // manager.getAllProofs().values().forEach(proof -> proof.interpretScript());

                MainController controller = new MainController(manager, SYNTAX_HIGHLIGHTING_EXECUTOR);

                primaryStage.close();
                Scene scene = new Scene(controller.getView());
                scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
                substage = new Stage();
                substage.setScene(scene);
                substage.setWidth(900);
                substage.setHeight(700);
                substage.setTitle("AlgoVer - " + projectFile);
                substage.show();
            } else {
                primaryStage.show();
            }



        } catch (FormatException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (DafnyParserException e) {
            e.printStackTrace();
        }

    }


    private void createConfigurationAndLoadProject(ActionEvent actionEvent) {


    }

}
