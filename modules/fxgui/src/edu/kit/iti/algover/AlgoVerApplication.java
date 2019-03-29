/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import com.jfoenix.controls.JFXButton;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.*;
import edu.kit.iti.algover.settings.GeneralSettingsController;
import edu.kit.iti.algover.settings.ISettingsController;
import edu.kit.iti.algover.settings.ProjectSettingsController;
import edu.kit.iti.algover.settings.SettingsFactory;
import edu.kit.iti.algover.util.FormatException;
import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.DirectoryChooser;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Optional;
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
        pane.setPrefSize(200.0,200.0);
        VBox vbox= new VBox();
        vbox.setSpacing(50);
        vbox.setAlignment(Pos.CENTER);
        HBox buttonBox = new HBox();
        buttonBox.setAlignment(Pos.CENTER);
        buttonBox.setSpacing(50);

        String text = "<h1>Welcome to AlgoVer</h1> " +
                "<p>A seamless verification system for Dafny programs created at Karlsruhe Institute of Technology (KIT)." +
                "</p><br>" ;
//                "<p> For more information on the Dafny langauage visit " +
//                "<a href=\"https://www.microsoft.com/en-us/research/project/dafny-a-language-and-program-verifier-for-functional-correctness/\">Microsoft's Dafny-Webpage</a>." +
//                "For more information on special Dafny support visit TODO";
        WebView webView = new WebView();
        WebEngine engine = webView.getEngine();
        engine.loadContent(text);


        //Buttons
        Button openFileChooser = new Button("Open existing project");
        openFileChooser.setOnAction(this::handleFileChooserAction);
        openFileChooser.setPrefHeight(buttonBox.getHeight());

        Button createProject = new Button("Create new project");
        createProject.setOnAction(this::createNewProjectHandler);
        createProject.setPrefHeight(buttonBox.getHeight());

        Button openEmptyProject = new Button("Create empty project");
        openEmptyProject.setOnAction(handleEmptyProjectCreation(primaryStage));
        openEmptyProject.setPrefHeight(buttonBox.getHeight());

        buttonBox.setSpacing(30);
        buttonBox.getChildren().addAll(openEmptyProject, createProject, openFileChooser);
        vbox.getChildren().addAll(webView, buttonBox);
        pane.setCenter(vbox);

        primaryStage.setScene(new Scene(pane));
        primaryStage.setWidth(900);
        primaryStage.setHeight(700);
        primaryStage.show();


    }

    private EventHandler<ActionEvent> handleEmptyProjectCreation(Stage primaryStage) {
        return event -> {
            DirectoryChooser dirChooser = new DirectoryChooser();

            dirChooser.setInitialDirectory(new File("doc/examples/"));
            dirChooser.setTitle("Select directory");
            //first select a directory
            File file = dirChooser.showDialog(primaryStage);


            if(file != null){
                System.out.println("file = " + file);
                //then a filename
                TextInputDialog dialog = new TextInputDialog("program.dfy");
                dialog.setTitle("Dafny file name");
                dialog.setHeaderText("Dafny file name");
                dialog.setContentText("Please enter the name for the empty Dafny file");
                Optional<String> filename = dialog.showAndWait();

                if (filename.isPresent()){
                    String s = file.getAbsolutePath() + File.separator + filename.get();
                    Path dfyMasterFile = null;
                    try {
                        dfyMasterFile = Files.createFile(Paths.get(s));
                        File file1 = dfyMasterFile.toFile();
                        DafnyProjectManager manager = new DafnyProjectManager(file1);
                        createAndExecuteMainController(file1, manager);
                    } catch (IOException e) {
                            e.printStackTrace();
                        } catch (DafnyParserException e) {
                            e.printStackTrace();
                        }
                    }


            }

        };
    }


    private void createAndShowConfigPane(Stage substage) {
        Configuration config = new Configuration();
        Optional<ISettingsController> collect = SettingsFactory.getSettingsPanel(config).stream()
                .filter(node -> node.getName().equals(ProjectSettingsController.NAME))
                .findAny();

        if(collect.isPresent()){
            BorderPane configPane = new BorderPane();
            //configPane.setPrefSize(400.0, 400.0);
            //configPane.setCenter(collect.get(0));
            ScrollPane scrollPane = new ScrollPane();
            scrollPane.setFitToWidth(true);
            //scrollPane.setFitToHeight(true);
            scrollPane.setContent(collect.get().getNode());

            configPane.setCenter(scrollPane);
            //Buttons
            ButtonBar buttonBar = new ButtonBar();
            Button applyConfig = new Button("Create Configuration");
            ButtonBar.setButtonData(applyConfig, ButtonBar.ButtonData.APPLY);
            applyConfig.setOnAction(event -> {
                collect.get().save();
            });

            Button cancelButton = new Button("Cancel");
            cancelButton.setOnAction(event ->
            {
                createAndShowWelcomePane(substage);
            });
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

                createAndExecuteMainController(projectFile, manager);
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

    private void createAndExecuteMainController(File projectFile, ProjectManager manager) {
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
    }


    private void createConfigurationAndLoadProject(ActionEvent actionEvent) {
        //TODO Controller?

    }

}
