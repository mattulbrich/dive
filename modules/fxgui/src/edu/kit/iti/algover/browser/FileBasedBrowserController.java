/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.OtherEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.Proof;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.TreeItem;

import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public class FileBasedBrowserController extends BrowserController {

    public FileBasedBrowserController(Project project, Map<String, Proof> proofsByPVC, PVCClickEditListener engagedListener) {
        super(project, proofsByPVC, engagedListener);
    }

    protected void populateTreeTable() {
        TreeTableEntity dafnyFiles = new OtherEntity("Dafny Files", getDafnyFileEntities());

        TreeItem<TreeTableEntity> dafnyFilesItem = createTreeItem(dafnyFiles);
        getView().setRoot(dafnyFilesItem);
    }

    public List<TreeTableEntity> getDafnyFileEntities() {
        return getProject().getDafnyFiles().stream()
                .filter(Predicate.not(DafnyDecl::isInLibrary))
                .map(this::getEntityFromFile)
                .collect(Collectors.toList());
    }
}
