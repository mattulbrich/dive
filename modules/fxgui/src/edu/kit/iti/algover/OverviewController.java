package edu.kit.iti.algover;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.entities.*;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;

/**
 * Created by philipp on 27.06.17.
 */
public class OverviewController {

    private final Project project;
    private final BrowserController browserController;
    private final EditorController editorController;
    private final TimelineLayout view;

    public OverviewController(Project project) {
        this.project = project;
        this.browserController = new FlatBrowserController(project);
        //this.browserController = new FileBasedBrowserController(project);
        this.editorController = new EditorController();

        this.view = new TimelineLayout(browserController.getView(), editorController.getView());
        view.setDividerPosition(0.2);

        browserController.setSelectionListener(this::onBrowserItemSelected);
    }

    private void onBrowserItemSelected(TreeTableEntity treeTableEntity) {
        DafnyFile file = treeTableEntity.getLocation();
        if (file != null) {
            editorController.viewFile(file);
            PVC pvc = treeTableEntity.accept(new PVCGetterVisitor());
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

    public TimelineLayout getView() {
        return view;
    }
}
