package edu.kit.iti.algover.overview;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.Collection;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FileBasedOverviewController extends OverviewController {

    protected FileBasedOverviewController(Project project) {
        super(project);
    }

    protected void populateTreeTable() {
        TreeTableEntity dafnyFiles = createNewEntity(TreeTableEntity.Kind.OTHER, "Dafny Files");
        TreeItem<TreeTableEntity> dafnyFilesItem = new TreeItem<>(dafnyFiles);
        getView().setRoot(dafnyFilesItem);

        dafnyFilesItem.getChildren().setAll(getDafnyFileItems());
    }

    public Collection<TreeItem<TreeTableEntity>> getDafnyFileItems() {
        return getProject().getDafnyFiles().stream()
                .map(this::getItemFromFile)
                .collect(Collectors.toList());
    }
}
