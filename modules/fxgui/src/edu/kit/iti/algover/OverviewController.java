package edu.kit.iti.algover;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FileBasedBrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import javafx.scene.control.SplitPane;

/**
 * Created by philipp on 27.06.17.
 */
public class OverviewController {

    private final Project project;
    private final BrowserController browserController;
    private final EditorController editorController;
    private final SplitPane view;

    public OverviewController(Project project) {
        this.project = project;
        this.browserController = new FlatBrowserController(project);
        //this.browserController = new FileBasedBrowserController(project);
        this.editorController = new EditorController();
        this.view = new SplitPane(browserController.getView(), editorController.getView());
        view.setDividerPositions(0.2);

        browserController.setSelectionListener(this::onBrowserItemSelected);
    }

    private void onBrowserItemSelected(TreeTableEntity treeTableEntity) {
        DafnyFile file = treeTableEntity.getLocation();
        if (file != null) {
            editorController.viewFile(file);
            PVC pvc = treeTableEntity.getPvc();
            if (pvc != null) {
                editorController.viewPVCSelection(pvc);
            } else {
                editorController.resetPVCSelection();
            }
        }
    }

    public Project getProject() {
        return project;
    }

    public SplitPane getView() {
        return view;
    }
}
