package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.OtherEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FlatBrowserController extends BrowserController {

    public FlatBrowserController(Project project) {
        super(project);
    }

    protected void populateTreeTable() {
        TreeTableEntity rootNode = new OtherEntity("root");

        TreeItem<TreeTableEntity> root = new TreeItem<>(rootNode);
        getView().setRoot(root);
        getView().setShowRoot(false);

        root.getChildren().setAll(
                createClassesTreeItem(),
                createMethodsTreeItem()
        );
    }

    private TreeItem<TreeTableEntity> createMethodsTreeItem() {
        TreeTableEntity methods = new OtherEntity("Methods");
        TreeItem<TreeTableEntity> methodsItem = new TreeItem<>(methods);
        methodsItem.getChildren().setAll(
                getProject().getMethods().stream()
                    .map(dafnyMethod -> getItemFromMethod(findFileWithMethod(dafnyMethod), dafnyMethod))
                    .collect(Collectors.toList())
        );
        return methodsItem;
    }

    private TreeItem<TreeTableEntity> createClassesTreeItem() {
        TreeTableEntity classes = new OtherEntity("Classes");
        TreeItem<TreeTableEntity> classesItem = new TreeItem<>(classes);
        classesItem.getChildren().setAll(
                getProject().getClasses().stream()
                    .map(dafnyClass -> getItemFromClass(findFileWithClass(dafnyClass), dafnyClass))
                    .collect(Collectors.toList())
        );
        return classesItem;
    }

    private DafnyFile findFileWithMethod(DafnyMethod dafnyMethod) {
        return getProject().getDafnyFiles().stream()
            .filter(dafnyFile -> dafnyFile.getMethods().contains(dafnyMethod))
            .findFirst()
            .orElse(null);
    }

    private DafnyFile findFileWithClass(DafnyClass dafnyClass) {
        return getProject().getDafnyFiles().stream()
            .filter(dafnyFile -> dafnyFile.getClasses().contains(dafnyClass))
            .findFirst()
            .orElse(null);
    }

}
