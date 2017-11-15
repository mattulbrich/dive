package edu.kit.iti.algover;

import edu.kit.iti.algover.util.FormatException;
import javafx.application.Application;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public abstract class ApplicationTest extends Application {

    // Used for calculating the syntax highlighting asynchronously
    protected static final ExecutorService SYNTAX_HIGHLIGHTING_EXECUTOR = Executors.newSingleThreadExecutor();

    @Override
    public void start(Stage stage) throws Exception {
        Scene scene = new Scene(constructView());
        scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        stage.setScene(scene);
        stage.setWidth(900);
        stage.setHeight(700);
        stage.show();
    }

    protected abstract Parent constructView() throws FormatException;

    @Override
    public void stop() throws Exception {
        SYNTAX_HIGHLIGHTING_EXECUTOR.shutdown();
    }

}
