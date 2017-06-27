package edu.kit.iti.algover;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.project.Project;
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
        // this.browserController = new FileBasedBrowserController(project);
        this.editorController = new EditorController(project.getBaseDir());
        this.view = new SplitPane(browserController.getView(), editorController.getView());
        view.setDividerPositions(0.2);

        browserController.setSelectionListener(this::onBrowserItemSelected);
    }

    private void onBrowserItemSelected(TreeTableEntity treeTableEntity) {
        String file = figureOutFile(treeTableEntity);
        if (file != null) {
            editorController.viewFile(file);
        }
    }

    private String figureOutFile(TreeTableEntity entity) {
        switch (entity.getKind()) {
            case CLASS:
                DafnyClass dafnyClass = project.getClass(entity.getName());
                if (dafnyClass == null) return null;
                return dafnyClass.getFilename();
            case METHOD:
                DafnyMethod dafnyMethod = project.getMethod(entity.getName());
                if (dafnyMethod == null) {
                    dafnyMethod = project.getClasses().stream()
                            .flatMap(aClass -> aClass.getMethods().stream())
                            .filter(method -> method.getName().equals(entity.getName()))
                            .findFirst().orElse(null);
                    if (dafnyMethod == null) return null;
                }
                return dafnyMethod.getFilename();
            case OTHER:
                // maybe its a file that was clicked on
                if (entity.getName().endsWith(".dfy")) {
                    return entity.getName();
                } else {
                    return null;
                }
            default: return null;
        }
    }

    public Project getProject() {
        return project;
    }

    public SplitPane getView() {
        return view;
    }
}
