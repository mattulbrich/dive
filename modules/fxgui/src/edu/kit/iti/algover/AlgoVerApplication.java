/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.project.DafnyProjectManager;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.DirectoryChooser;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

import java.awt.*;
import java.io.File;
import java.util.List;
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
                return;
            }
        } else {
            projectFile = new File(fileNames.get(0)).getAbsoluteFile();
        }

        ProjectManager manager;
        if (projectFile.getName().endsWith(".xml")) {
            // Read all PVCs and update GUId
            manager = new XMLProjectManager(projectFile.getParentFile(), projectFile.getName());
        } else if(projectFile.getName().endsWith(".dfy")) {
            manager = new DafnyProjectManager(projectFile);
        } else {
            throw new IllegalArgumentException("AlgoVer supports only .dfy and .xml files.");
        }

        // TODO Maybe don't do this initially (might hurt UX, when there are a lot of proofs)
        // manager.getAllProofs().values().forEach(proof -> proof.interpretScript());

        MainController controller = new MainController(manager, SYNTAX_HIGHLIGHTING_EXECUTOR);

        Scene scene = new Scene(controller.getView());
        scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        primaryStage.setScene(scene);

        Dimension screenSize = java.awt.Toolkit.getDefaultToolkit().getScreenSize();
        double width = screenSize.getWidth();
        double height = screenSize.getHeight();
        primaryStage.setWidth(width);
        primaryStage.setHeight(height);
        primaryStage.setTitle("AlgoVer - " + projectFile);
        primaryStage.show();

    }


    @Override
    public void stop() throws Exception {
        SYNTAX_HIGHLIGHTING_EXECUTOR.shutdown();
    }
}
