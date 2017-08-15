package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.OtherEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import javafx.scene.control.TreeItem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FlatBrowserController extends BrowserController {

    public FlatBrowserController(Project project, TreeTableEntityEngagedListener engagedListener) {
        super(project, engagedListener);
    }

    protected void populateTreeTable() {
        TreeTableEntity rootEntity = new OtherEntity("root",
                Arrays.asList(createClassesEntity(), createMethodsEntity()));

        TreeItem<TreeTableEntity> root = createTreeItem(rootEntity);
        getView().setRoot(root);
        getView().setShowRoot(false);

    }

    private TreeTableEntity createMethodsEntity() {
        List<TreeTableEntity> children = new ArrayList<>();
        getProject().getMethods().stream()
            .map(dafnyMethod -> getEntityFromMethod(findFileWithMethod(dafnyMethod), dafnyMethod))
            .forEach(children::add);

        return new OtherEntity("Methods", children);
    }

    private TreeTableEntity createClassesEntity() {
        List<TreeTableEntity> children = new ArrayList<>();
        getProject().getClasses().stream()
            .map(dafnyClass -> getEntityFromClass(findFileWithClass(dafnyClass), dafnyClass))
            .forEach(children::add);

        return new OtherEntity("Classes", children);
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
