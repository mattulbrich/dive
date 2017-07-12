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

import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
public abstract class BrowserController {

    private final Project project;
    private final BrowserTreeTable view;

    private BrowserSelectionListener selectionListener;

    protected BrowserController(Project project) {
        this.project = project;
        this.view = new BrowserTreeTable();

        view.getSelectionModel().selectedItemProperty().addListener(this::onTreeItemSelected);

        populateTreeTable();
    }

    protected abstract void populateTreeTable();

    protected TreeItem<TreeTableEntity> getItemFromFile(DafnyFile dafnyFile) {
        TreeItem<TreeTableEntity> item = new TreeItem<>(new FileEntity(dafnyFile));
        item.getChildren().addAll(
            dafnyFile.getClasses().stream()
                .map(dafnyClass -> getItemFromClass(dafnyFile, dafnyClass))
                .collect(Collectors.toList()));
        item.getChildren().addAll(
            dafnyFile.getMethods().stream()
                .map(dafnyMethod -> getItemFromMethod(dafnyFile, dafnyMethod))
                .collect(Collectors.toList()));
        return item;
    }

    protected TreeItem<TreeTableEntity> getItemFromClass(DafnyFile dafnyFile, DafnyClass dafnyClass) {
        TreeItem<TreeTableEntity> item = new TreeItem<>(new ClassEntity(dafnyClass, dafnyFile));
        item.getChildren().setAll(
            dafnyClass.getMethods().stream()
                .map(dafnyMethod -> getItemFromMethod(dafnyFile, dafnyMethod))
                .collect(Collectors.toList()));
        return item;
    }

    protected TreeItem<TreeTableEntity> getItemFromMethod(DafnyFile dafnyFile, DafnyMethod dafnyMethod) {
        TreeItem<TreeTableEntity> item = new TreeItem<>(new MethodEntity(dafnyMethod, dafnyFile));
        PVCCollection collection = project.getVerificationConditionsFor(dafnyMethod);
        if (collection != null) {
            item.getChildren().setAll(
                collection.getChildren().stream()
                    .map(pvcCollection -> getItemFromPVC(dafnyFile, pvcCollection))
                    .collect(Collectors.toList()));
        }
        return item;
    }

    private TreeItem<TreeTableEntity> getItemFromPVC(DafnyFile dafnyFile, PVCCollection pvcCollection) {
        if (pvcCollection.isPVCLeaf()) {
            PVC pvc = ((SinglePVC) pvcCollection).getPVC();
            return new TreeItem<>(new PVCEntity(pvc, dafnyFile));
        } else {
            TreeItem<TreeTableEntity> item = new TreeItem<>(new PVCGroupEntity((PVCGroup) pvcCollection, dafnyFile));
            item.getChildren().setAll(
                pvcCollection.getChildren().stream()
                    .map(subPvcCollection -> getItemFromPVC(dafnyFile, subPvcCollection))
                    .collect(Collectors.toList()));
            return item;
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
