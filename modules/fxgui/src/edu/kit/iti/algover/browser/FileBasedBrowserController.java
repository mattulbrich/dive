package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.OtherEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FileBasedBrowserController extends BrowserController {

    public FileBasedBrowserController(Project project, PVCClickEditListener engagedListener) {
        super(project, engagedListener);
    }

    protected void populateTreeTable() {
        TreeTableEntity dafnyFiles = new OtherEntity("Dafny Files", getDafnyFileEntities());

        TreeItem<TreeTableEntity> dafnyFilesItem = createTreeItem(dafnyFiles);
        getView().setRoot(dafnyFilesItem);
    }

    public List<TreeTableEntity> getDafnyFileEntities() {
        return getProject().getDafnyFiles().stream()
                .map(this::getEntityFromFile)
                .collect(Collectors.toList());
    }
}
