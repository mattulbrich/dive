/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.Stage;

import java.awt.*;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * @author Philipp (15.06.2017)
 * @author Extended by S.Grebing (March 2019)
 */
public class AlgoVerApplication extends Application {

    private Stage primaryStage;

    private Stage substage;

    public static void main(String[] args) {
        launch(args);
    }

    // Used for calculating the syntax highlighting asynchronously
    public static final ExecutorService SYNTAX_HIGHLIGHTING_EXECUTOR = Executors.newSingleThreadExecutor();



    @Override
    public void start(Stage primaryStage) throws Exception {
        this.primaryStage = primaryStage;
        //create Welcome Dialog
        Parameters params = getParameters();
        List<String> fileNames = params.getUnnamed();
        if(fileNames != null && fileNames.size() > 0){
           // File absoluteFile = new File(fileNames.get(0)).getAbsoluteFile();
           // createAndExecuteMainController(absoluteFile, createProjectManager(absoluteFile));
            startApplication(primaryStage, fileNames);
        } else {
            startApplication(primaryStage, Collections.emptyList());
        }
    }

    /**
     * If opendirectly is empty, a welcome pane view is created. Otherwise the application is started directly with
     * the parameters in the list opendirectly
     * @param primaryStage
     * @param opendirectly
     */
    private void startApplication(Stage primaryStage, List<String> opendirectly) {
        primaryStage.setTitle("AlgoVer");
        WelcomePane p = new WelcomePane(primaryStage, opendirectly);
        primaryStage.setScene(new Scene(p.getRootPane()));

        Dimension screenSize = java.awt.Toolkit.getDefaultToolkit().getScreenSize();
        double width = screenSize.getWidth();
        double height = screenSize.getHeight();
        primaryStage.setWidth(width);
        primaryStage.setHeight(height);
        primaryStage.show();

    }


    @Override
    public void stop() throws Exception {
        SYNTAX_HIGHLIGHTING_EXECUTOR.shutdown();
    }
}
