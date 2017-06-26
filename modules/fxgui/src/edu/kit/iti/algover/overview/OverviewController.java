package edu.kit.iti.algover.overview;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public abstract class OverviewController {

    private final Project project;
    private final OverviewTreeTable view;

    protected OverviewController(Project project) {
        this.project = project;
        this.view = new OverviewTreeTable();

        populateTreeTable();
    }

    protected abstract void populateTreeTable();

    protected TreeTableEntity createNewEntity(TreeTableEntity.Kind kind, String name) {
        return new TreeTableEntity(
                name,
                0,
                TreeTableEntity.ProofStatus.UNPROVEN,
                kind);
    }

    protected TreeItem<TreeTableEntity> getItemFromFile(DafnyFile dafnyFile) {
        TreeTableEntity file = createNewEntity(TreeTableEntity.Kind.OTHER, dafnyFile.getName());
        TreeItem<TreeTableEntity> item = new TreeItem<>(file);
        item.getChildren().addAll(dafnyFile.getClasses().stream().map(this::getItemFromClass).collect(Collectors.toList()));
        item.getChildren().addAll(dafnyFile.getMethods().stream().map(this::getItemFromMethod).collect(Collectors.toList()));
        return item;
    }

    protected TreeItem<TreeTableEntity> getItemFromClass(DafnyClass dafnyClass) {
        TreeTableEntity clazz = createNewEntity(TreeTableEntity.Kind.CLASS, dafnyClass.getName());
        TreeItem<TreeTableEntity> item = new TreeItem<>(clazz);
        item.getChildren().setAll(dafnyClass.getMethods().stream().map(this::getItemFromMethod).collect(Collectors.toList()));
        return item;
    }

    protected TreeItem<TreeTableEntity> getItemFromMethod(DafnyMethod dafnyMethod) {
        TreeTableEntity method = createNewEntity(TreeTableEntity.Kind.METHOD, dafnyMethod.getName());
        return new TreeItem<>(method);
    }

    public OverviewTreeTable getView() {
        return view;
    }

    public Project getProject() {
        return project;
    }
}
