package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.OtherEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.Collection;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FileBasedBrowserController extends BrowserController {

    public FileBasedBrowserController(Project project) {
        super(project);
    }

    protected void populateTreeTable() {
        TreeTableEntity dafnyFiles = new OtherEntity("Dafny Files");
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
