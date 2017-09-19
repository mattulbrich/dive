package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.*;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.SinglePVC;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.TreeItem;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public abstract class BrowserController {

    private final Project project;
    private final BrowserTreeTable view;

    private BrowserSelectionListener selectionListener;

    protected BrowserController(Project project, PVCClickEditListener editListener) {
        this.project = project;
        this.view = new BrowserTreeTable(editListener);

        view.getSelectionModel().selectedItemProperty()
                .addListener(this::onTreeItemSelected);

        populateTreeTable();
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
        return new ClassEntity(dafnyClass, dafnyFile, children);
    }

    protected TreeTableEntity getEntityFromMethod(DafnyFile dafnyFile, DafnyMethod dafnyMethod) {
        List<TreeTableEntity> children = new ArrayList<>();
        PVCCollection collection = project.getVerificationConditionsFor(dafnyMethod);
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
            return new PVCEntity(pvc, dafnyFile);
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
}
