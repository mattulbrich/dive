package edu.kit.iti.algover.overview;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FlatOverviewController {

    private final Project project;
    private final OverviewTreeTable view;

    public FlatOverviewController(Project project) {
        this.project = project;
        this.view = new OverviewTreeTable();

        populateTreeTable();
    }

    private void populateTreeTable() {
        TreeTableEntity rootNode = createNewEntity(TreeTableEntity.Kind.OTHER, "root");

        TreeItem<TreeTableEntity> root = new TreeItem<>(rootNode);
        view.setRoot(root);
        view.setShowRoot(false);

        root.getChildren().setAll(
                createClassesTreeItem(),
                createMethodsTreeItem()
        );
    }

    private TreeItem<TreeTableEntity> createMethodsTreeItem() {
        TreeTableEntity methods = createNewEntity(TreeTableEntity.Kind.OTHER, "Methods");
        TreeItem<TreeTableEntity> methodsItem = new TreeItem<>(methods);
        methodsItem.getChildren().setAll(
                project.getMethods().stream().map(this::itemFromMethod).collect(Collectors.toList())
        );
        return methodsItem;
    }

    private TreeItem<TreeTableEntity> itemFromMethod(DafnyMethod dafnyMethod) {
        return new TreeItem<>(createNewEntity(TreeTableEntity.Kind.METHOD, dafnyMethod.getName()));
    }

    private TreeItem<TreeTableEntity> createClassesTreeItem() {
        TreeTableEntity classes = createNewEntity(TreeTableEntity.Kind.OTHER, "Classes");
        TreeItem<TreeTableEntity> classesItem = new TreeItem<>(classes);
        classesItem.getChildren().setAll(
                project.getClasses().stream().map(this::itemFromClass).collect(Collectors.toList())
        );
        return classesItem;
    }

    private TreeItem<TreeTableEntity> itemFromClass(DafnyClass dafnyClass) {
        return new TreeItem<>(createNewEntity(TreeTableEntity.Kind.CLASS, dafnyClass.getName()));
    }

    private TreeTableEntity createNewEntity(TreeTableEntity.Kind kind, String name) {
        return new TreeTableEntity(
                name,
                0,
                TreeTableEntity.ProofStatus.UNPROVEN,
                kind);
    }

    public OverviewTreeTable getView() {
        return view;
    }
}
