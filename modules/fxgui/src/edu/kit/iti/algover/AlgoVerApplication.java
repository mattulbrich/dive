package edu.kit.iti.algover;

import edu.kit.iti.algover.editor.EditorView;
import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.project.Project;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.stage.DirectoryChooser;
import javafx.stage.Stage;

import java.io.File;

/**
 * Created by Philipp on 15.06.2017.
 */
public class AlgoVerApplication extends Application {

    @Override
    public void start(Stage primaryStage) throws Exception {
        // Let user choose a project directory
        DirectoryChooser chooser = new DirectoryChooser();
        chooser.setTitle("Choose project");
        chooser.setInitialDirectory(new File("modules/fxgui/test-res/edu/kit/iti/algover"));
        File projectDir = chooser.showDialog(primaryStage);

        // Read all PVCs and update GUI
        Project project = ProjectFacade.getInstance().buildProject(projectDir);

        BrowserController controller = new FlatBrowserController(project);
        // BrowserController controller = new FileBasedBrowserController(project);

        SplitPane pane = new SplitPane(controller.getView(), new EditorView());
        Scene scene = new Scene(pane);
        scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        primaryStage.setScene(scene);
        primaryStage.show();

    }
}
