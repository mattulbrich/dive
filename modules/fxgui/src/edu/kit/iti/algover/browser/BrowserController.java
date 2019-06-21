/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.*;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.*;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.TreeItem;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Controller for the PVC and System Structure Overview
 * @author Philipp Krüger (on 26.06.17)
 * @author S. Grebing (added ContextMenu)
 */
public abstract class BrowserController {

    private Project project;
    private final BrowserTreeTable view;
    private Map<String, Proof> proofsByPVC;

    private BrowserSelectionListener selectionListener;

    protected BrowserController(Project project, Map<String, Proof> proofsByPVC, PVCClickEditListener editListener) {
        this.project = project;
        this.proofsByPVC = proofsByPVC;
        this.view = new BrowserTreeTable(editListener);

        view.getSelectionModel().selectedItemProperty()
                .addListener(this::onTreeItemSelected);
        createContextMenu(view.getContextMenu());
        populateTreeTable();
    }

    private void createContextMenu(ContextMenu contextMenu) {
        MenuItem expandSubtree = new MenuItem("Expand Tree");
        expandSubtree.setOnAction(event -> {
            if(selectionListener != null){
                TreeItem<TreeTableEntity> selectedItem = getView().getSelectionModel().getSelectedItem();
                expandCollapseTree(selectedItem, true);
            }
        });

        MenuItem collapseSubtree = new MenuItem("Collapse Tree");
        collapseSubtree.setOnAction(event -> {
            if(selectionListener != null){
                TreeItem<TreeTableEntity> selectedItem = getView().getSelectionModel().getSelectedItem();
                expandCollapseTree(selectedItem, false);
            }
        });


        contextMenu.getItems().addAll(new SeparatorMenuItem(), expandSubtree, collapseSubtree);

    }

    public void expandCollapseTree(TreeItem<TreeTableEntity> item, boolean expand){
    if(item != null && !item.isLeaf()){
        item.setExpanded(expand);
        for(TreeItem<TreeTableEntity> child : item.getChildren()){
            expandCollapseTree(child, expand);
        }
    }
}

    public ContextMenu getBrowserContextMenu(){
        return view.getContextMenu();
    }

    protected abstract void populateTreeTable();

    protected TreeTableEntity getEntityFromFile(DafnyFile dafnyFile) {
        List<TreeTableEntity> children = new ArrayList<>();
        children.addAll(
                dafnyFile.getClasses().stream()
                        .map(dafnyClass -> getEntityFromClass(dafnyFile, dafnyClass))
                        .collect(Collectors.toList()));
        children.addAll(
                dafnyFile.getMethods().stream()
                        .map(dafnyMethod -> getEntityFromMethod(dafnyFile, dafnyMethod))
                        .collect(Collectors.toList()));
        return new FileEntity(dafnyFile, children);
    }

    protected TreeTableEntity getEntityFromClass(DafnyFile dafnyFile, DafnyClass dafnyClass) {
        List<TreeTableEntity> children = new ArrayList<>();
        dafnyClass.getMethods().stream()
                .map(dafnyMethod -> getEntityFromMethod(dafnyFile, dafnyMethod))
                .forEach(children::add);
        dafnyClass.getFunctions().stream()
                .map(dafnyFunction -> getEntityFromFunction(dafnyFile, dafnyFunction))
                .forEach(children::add);
        return new ClassEntity(dafnyClass, dafnyFile, children);
    }

    protected TreeTableEntity getEntityFromFunction(DafnyFile dafnyFile, DafnyFunction dafnyFunction) {
        List<TreeTableEntity> children = new ArrayList<>();
        PVCCollection collection = project.getPVCsFor(dafnyFunction);
        if (collection != null) {

            collection.getChildren().stream()
                    .map(pvcCollection -> getEntityFromPVC(dafnyFile, pvcCollection))
                    .forEach(children::add);
        }
        return new FunctionEntity(dafnyFunction, dafnyFile, children);
    }

    protected TreeTableEntity getEntityFromMethod(DafnyFile dafnyFile, DafnyMethod dafnyMethod) {
        List<TreeTableEntity> children = new ArrayList<>();
        PVCCollection collection = project.getPVCsFor(dafnyMethod);
        if (collection != null) {

            collection.getChildren().stream()
                    .map(pvcCollection -> getEntityFromPVC(dafnyFile, pvcCollection))
                    .forEach(children::add);
        }
        return new MethodEntity(dafnyMethod, dafnyFile, children);
    }

    private TreeTableEntity getEntityFromPVC(DafnyFile dafnyFile, PVCCollection pvcCollection) {
        if (pvcCollection.isPVCLeaf()) {
            PVC pvc = ((SinglePVC) pvcCollection).getPVC();
            return new PVCEntity(proofsByPVC.get(pvc.getIdentifier()), pvc, dafnyFile);
        } else {
            List<TreeTableEntity> children = new ArrayList<>();
            pvcCollection.getChildren().stream()
                    .map(subPvcCollection -> getEntityFromPVC(dafnyFile, subPvcCollection))
                    .forEach(children::add);
            return new PVCGroupEntity((PVCGroup) pvcCollection, dafnyFile, children);
        }
    }

    protected void onTreeItemSelected(
            ObservableValue<? extends TreeItem<TreeTableEntity>> value,
            TreeItem<TreeTableEntity> before,
            TreeItem<TreeTableEntity> item) {
        TreeTableEntity entity = entityFromTreeItem(item);
        if (entity == null || selectionListener == null) return;
        selectionListener.onBrowserItemSelected(entity);
    }

    protected TreeItem<TreeTableEntity> createTreeItem(TreeTableEntity entity) {
        List<TreeItem<TreeTableEntity>> children =
                entity.getChildren().stream()
                        .map(this::createTreeItem)
                        .collect(Collectors.toList());

        TreeItem<TreeTableEntity> item = new TreeItem<>(entity);
        item.getChildren().setAll(children);
        return item;
    }

    protected TreeTableEntity entityFromTreeItem(TreeItem<TreeTableEntity> item) {
        if (item == null) return null;
        return item.getValue();
    }

    public BrowserTreeTable getView() {
        return view;
    }

    public Project getProject() {
        return project;
    }

    public BrowserSelectionListener getSelectionListener() {
        return selectionListener;
    }

    public void setSelectionListener(BrowserSelectionListener selectionListener) {
        this.selectionListener = selectionListener;
    }

    public void onRefresh(Project project, Map<String, Proof> proofsByPVC) {
        this.project = project;
        this.proofsByPVC = proofsByPVC;
        populateTreeTable();
    }
}
