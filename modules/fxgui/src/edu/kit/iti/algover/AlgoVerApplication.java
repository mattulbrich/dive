package edu.kit.iti.algover;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.Debug;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.DirectoryChooser;
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
        DirectoryChooser chooser = new DirectoryChooser();
        chooser.setTitle("Choose project");
        chooser.setInitialDirectory(new File("modules/fxgui/test-res/edu/kit/iti/algover"));
        File projectDir = chooser.showDialog(primaryStage);

        // Read all PVCs and update GUI
        Project project = ProjectFacade.getInstance().buildProject(projectDir);
        project.generateAndCollectPVC();

        OverviewController controller = new OverviewController(project);
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
