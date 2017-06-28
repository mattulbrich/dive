package edu.kit.iti.algover;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.project.Project;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.DirectoryChooser;
import javafx.stage.Stage;

import java.io.File;
import java.util.concurrent.Executor;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Created by Philipp on 15.06.2017.
 */
public class AlgoVerApplication extends Application {

    public static final ExecutorService EXECUTOR = Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors());

    @Override
    public void start(Stage primaryStage) throws Exception {
        // Let user choose a project directory
        DirectoryChooser chooser = new DirectoryChooser();
        chooser.setTitle("Choose project");
        chooser.setInitialDirectory(new File("modules/fxgui/test-res/edu/kit/iti/algover"));
        File projectDir = chooser.showDialog(primaryStage);

        // Read all PVCs and update GUI
        Project project = ProjectFacade.getInstance().buildProject(projectDir);

        OverviewController controller = new OverviewController(project);
        Scene scene = new Scene(controller.getView());
        scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        primaryStage.setScene(scene);
        primaryStage.setWidth(1000);
        primaryStage.setHeight(800);
        primaryStage.show();
    }

    @Override
    public void stop() throws Exception {
        EXECUTOR.shutdown();
    }
}
