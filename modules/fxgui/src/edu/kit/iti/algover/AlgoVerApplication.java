/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.DirectoryChooser;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

import java.io.File;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Created by Philipp on 15.06.2017.
 */
public class AlgoVerApplication extends Application {

    public static void main(String[] args) {
        launch(args);
    }

    // Used for calculating the syntax highlighting asynchronously
    private static final ExecutorService SYNTAX_HIGHLIGHTING_EXECUTOR = Executors.newSingleThreadExecutor();

    @Override
    public void start(Stage primaryStage) throws Exception {

        try {
            DirectoryChooser chooser = new DirectoryChooser();

            chooser.setTitle("Choose project folder");
            chooser.setInitialDirectory(new File("doc/examples/"));
            File projectFolder = chooser.showDialog(primaryStage);
            File projectConfigFile = new File(projectFolder.getAbsolutePath() + "/config.xml");
            if (!projectConfigFile.exists()) {
                System.out.println("Could not find config file in selected folder.");
                return;
            }

            // Read all PVCs and update GUI
            ProjectManager manager = new ProjectManager(projectConfigFile.getParentFile(), projectConfigFile.getName());
            // TODO Maybe don't do this initially (might hurt UX, when there are a lot of proofs)
            manager.getAllProofs().values().forEach(proof -> proof.interpretScript());

            MainController controller = new MainController(manager, SYNTAX_HIGHLIGHTING_EXECUTOR);

            Scene scene = new Scene(controller.getView());
            scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
            primaryStage.setScene(scene);
            primaryStage.setWidth(900);
            primaryStage.setHeight(700);
            primaryStage.show();

        } catch (NullPointerException npe) {
            System.out.println("There was a problem when loading a project. Please restart the program");
            System.exit(0);
        }
    }


    @Override
    public void stop() throws Exception {
        SYNTAX_HIGHLIGHTING_EXECUTOR.shutdown();
    }
}
