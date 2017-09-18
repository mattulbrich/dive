package edu.kit.iti.algover;

import com.sun.javafx.sg.prism.NGNode;
import edu.kit.iti.algover.project.ProjectManager;
import javafx.application.Application;
import javafx.scene.Camera;
import javafx.scene.ParallelCamera;
import javafx.scene.PerspectiveCamera;
import javafx.scene.Scene;
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
    public static final ExecutorService SH_EXECUTOR = Executors.newSingleThreadExecutor();

    @Override
    public void start(Stage primaryStage) throws Exception {
        // Let user choose a project directory
        FileChooser chooser = new FileChooser();
        chooser.setSelectedExtensionFilter(new FileChooser.ExtensionFilter("AlgoVer configuration xmls", "xml"));
        chooser.setTitle("Choose project config file");
        chooser.setInitialDirectory(new File("doc/examples/"));
        File projectConfigFile = chooser.showOpenDialog(primaryStage);

        // Read all PVCs and update GUI
        ProjectManager manager = new ProjectManager();
        manager.loadProject(projectConfigFile);

        OverviewController controller = new OverviewController(manager);
        Scene scene = new Scene(controller.getView());
        scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        primaryStage.setScene(scene);
        primaryStage.setWidth(900);
        primaryStage.setHeight(700);
        primaryStage.show();
    }

    @Override
    public void stop() throws Exception {
        SH_EXECUTOR.shutdown();
    }
}
