/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.Stage;

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
        startApplication(primaryStage, fileNames);
    }

    /**
     * If opendirectly is empty, a welcome pane view is created. Otherwise the application is started directly with
     * the parameters in the list opendirectly
     * @param primaryStage
     * @param opendirectly
     */
    public static void startApplication(Stage primaryStage, List<String> opendirectly) {
        // nicer font anti aliasing on Linux
        System.setProperty("prism.lcdtext", "false");
        System.setProperty("prism.text", "t2k");

        primaryStage.setTitle("DIVE");
        WelcomePane p = new WelcomePane(primaryStage, opendirectly);
        primaryStage.setScene(new Scene(p.getRootPane()));
        primaryStage.setWidth(1000);
        primaryStage.setHeight(900);
        primaryStage.show();

    }


    @Override
    public void stop() throws Exception {
        SYNTAX_HIGHLIGHTING_EXECUTOR.shutdown();
    }

}
