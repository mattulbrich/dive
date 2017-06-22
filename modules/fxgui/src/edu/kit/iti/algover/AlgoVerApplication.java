package edu.kit.iti.algover;

import edu.kit.iti.algover.facade.ProjectFacade;
import edu.kit.iti.algover.model.ProjectTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.Debug;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
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
    chooser.setInitialDirectory(new File("modules/core/test-res/edu/kit/iti/algover"));
    File projectDir = chooser.showDialog(primaryStage);

    // Read all PVCs and update GUI
    Project project = ProjectFacade.getInstance().buildProject(projectDir);

    ProjectTreeTableView view = new ProjectTreeTableView(project);
    primaryStage.setScene(new Scene(view));
    primaryStage.show();

  }
}
