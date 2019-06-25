/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.OtherEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.Proof;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.TreeItem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * Created by philipp on 26.06.17.
 */
public class FlatBrowserController extends BrowserController {

    public FlatBrowserController(Project project, Map<String, Proof> proofsByPVC, PVCClickEditListener engagedListener) {
        super(project, proofsByPVC, engagedListener);
    }

    protected void populateTreeTable() {
        TreeTableEntity rootEntity = new OtherEntity("root",
                Arrays.asList(createClassesEntity(), createMethodsEntity(), createFunctionsEntity()));

        TreeItem<TreeTableEntity> root = createTreeItem(rootEntity);
        getView().setRoot(root);
        getView().setShowRoot(false);

    }

    private TreeTableEntity createMethodsEntity() {
        List<TreeTableEntity> children = new ArrayList<>();
        getProject().getMethods().stream()
                .filter(NOT_IN_LIB_FILTER)
                .map(dafnyMethod -> getEntityFromMethod(findFileWithMethod(dafnyMethod), dafnyMethod))
                .forEach(children::add);

        return new OtherEntity("Methods", children);
    }

    private TreeTableEntity createFunctionsEntity() {
        List<TreeTableEntity> children = new ArrayList<>();
        getProject().getFunctions().stream()
                .filter(NOT_IN_LIB_FILTER)
                .map(dafnyFunction -> getEntityFromFunction(findFileWithFunction(dafnyFunction), dafnyFunction))
                .forEach(children::add);

        return new OtherEntity("Functions", children);
    }

    private TreeTableEntity createClassesEntity() {
        List<TreeTableEntity> children = new ArrayList<>();
        getProject().getClasses().stream()
                .filter(NOT_IN_LIB_FILTER)
                .map(dafnyClass -> getEntityFromClass(findFileWithClass(dafnyClass), dafnyClass))
                .forEach(children::add);

        return new OtherEntity("Classes", children);
    }

    private DafnyFile findFileWithMethod(DafnyMethod dafnyMethod) {
        return getProject().getDafnyFiles().stream()
                .filter(NOT_IN_LIB_FILTER)
                .filter(dafnyFile -> dafnyFile.getMethods().contains(dafnyMethod))
                .findFirst()
                .orElse(null);
    }

    private DafnyFile findFileWithFunction(DafnyFunction dafnyFunction) {
        return getProject().getDafnyFiles().stream()
                .filter(NOT_IN_LIB_FILTER)
                .filter(dafnyFile -> dafnyFile.getFunctions().contains(dafnyFunction))
                .findFirst()
                .orElse(null);
    }

    private DafnyFile findFileWithClass(DafnyClass dafnyClass) {
        return getProject().getDafnyFiles().stream()
                .filter(NOT_IN_LIB_FILTER)
                .filter(dafnyFile -> dafnyFile.getClasses().contains(dafnyClass))
                .findFirst()
                .orElse(null);
    }

}
