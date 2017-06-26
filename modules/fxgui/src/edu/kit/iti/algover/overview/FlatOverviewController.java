package edu.kit.iti.algover.overview;

import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FlatOverviewController extends OverviewController {

    public FlatOverviewController(Project project) {
        super(project);
    }

    protected void populateTreeTable() {
        TreeTableEntity rootNode = createNewEntity(TreeTableEntity.Kind.OTHER, "root");

        TreeItem<TreeTableEntity> root = new TreeItem<>(rootNode);
        getView().setRoot(root);
        getView().setShowRoot(false);

        root.getChildren().setAll(
                createClassesTreeItem(),
                createMethodsTreeItem()
        );
    }

    private TreeItem<TreeTableEntity> createMethodsTreeItem() {
        TreeTableEntity methods = createNewEntity(TreeTableEntity.Kind.OTHER, "Methods");
        TreeItem<TreeTableEntity> methodsItem = new TreeItem<>(methods);
        methodsItem.getChildren().setAll(
                getProject().getMethods().stream().map(this::getItemFromMethod).collect(Collectors.toList())
        );
        return methodsItem;
    }

    private TreeItem<TreeTableEntity> createClassesTreeItem() {
        TreeTableEntity classes = createNewEntity(TreeTableEntity.Kind.OTHER, "Classes");
        TreeItem<TreeTableEntity> classesItem = new TreeItem<>(classes);
        classesItem.getChildren().setAll(
                getProject().getClasses().stream().map(this::getItemFromClass).collect(Collectors.toList())
        );
        return classesItem;
    }

}
