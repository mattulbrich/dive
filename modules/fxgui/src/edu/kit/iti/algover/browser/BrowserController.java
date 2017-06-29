package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
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

    protected TreeTableEntity createNewEntity(DafnyFile loc, TreeTableEntity.Kind kind, String name) {
        return new TreeTableEntity(
                loc,
                name,
                0,
                TreeTableEntity.ProofStatus.UNPROVEN,
                kind);
    }

    protected TreeItem<TreeTableEntity> getItemFromFile(DafnyFile dafnyFile) {
        TreeTableEntity file = createNewEntity(dafnyFile, TreeTableEntity.Kind.OTHER, dafnyFile.getName());
        TreeItem<TreeTableEntity> item = new TreeItem<>(file);
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
        TreeTableEntity clazz = createNewEntity(dafnyFile, TreeTableEntity.Kind.CLASS, dafnyClass.getName());
        TreeItem<TreeTableEntity> item = new TreeItem<>(clazz);
        item.getChildren().setAll(
            dafnyClass.getMethods().stream()
                .map(dafnyMethod -> getItemFromMethod(dafnyFile, dafnyMethod))
                .collect(Collectors.toList()));
        return item;
    }

    protected TreeItem<TreeTableEntity> getItemFromMethod(DafnyFile dafnyFile, DafnyMethod dafnyMethod) {
        TreeTableEntity method = createNewEntity(dafnyFile, TreeTableEntity.Kind.METHOD, dafnyMethod.getName());
        TreeItem<TreeTableEntity> item = new TreeItem<>(method);
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
            TreeTableEntity pvcEntity = new TreeTableEntity(dafnyFile, pvc, TreeTableEntity.ProofStatus.UNPROVEN);
            return new TreeItem<>(pvcEntity);
        } else {
            TreeTableEntity pvc = createNewEntity(dafnyFile, TreeTableEntity.Kind.PVC, "Proof Verification Condition Group");
            TreeItem<TreeTableEntity> item = new TreeItem<>(pvc);
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
        if (item == null || selectionListener == null) return;
        TreeTableEntity entity = item.getValue();
        if (entity == null) return;
        selectionListener.onBrowserItemSelected(entity);
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
