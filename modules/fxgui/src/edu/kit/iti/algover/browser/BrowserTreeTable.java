package edu.kit.iti.algover.browser;


import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.TreeTableCell;
import javafx.scene.control.TreeTableColumn;
import javafx.scene.control.TreeTableView;

/**
 * Created by Philipp on 15.06.2017.
 */
public class BrowserTreeTable extends TreeTableView<TreeTableEntity> {

    private TreeTableColumn<TreeTableEntity, TreeTableEntity> nameColumn;
    private TreeTableColumn<TreeTableEntity, Float> percentageProvenColumn;
    private TreeTableColumn<TreeTableEntity, TreeTableEntity.ProofStatus> statusColumn;

    public BrowserTreeTable() {
        this.nameColumn = new TreeTableColumn<>("name");
        this.percentageProvenColumn = new TreeTableColumn<>("percentage proven");
        this.statusColumn = new TreeTableColumn<>("status");

        getStyleClass().addAll("browser");

        nameColumn.setCellValueFactory(this::nameCellFactory);
        percentageProvenColumn.setCellValueFactory(this::percentageProvenCellFactory);
        statusColumn.setCellValueFactory(this::statusCellFactory);

        nameColumn.setCellFactory(this::nameCellRenderer);

        nameColumn.setPrefWidth(200);
        percentageProvenColumn.setPrefWidth(50);

        super.getColumns().setAll(nameColumn, percentageProvenColumn, statusColumn);
    }

    private TreeTableCell<TreeTableEntity, TreeTableEntity> nameCellRenderer(TreeTableColumn<TreeTableEntity, TreeTableEntity> column) {
        return new NameCell();
    }

    private ObservableValue<TreeTableEntity> nameCellFactory(TreeTableColumn.CellDataFeatures<TreeTableEntity, TreeTableEntity> data) {
        return data.getValue().valueProperty();
    }

    private ObservableValue<Float> percentageProvenCellFactory(TreeTableColumn.CellDataFeatures<TreeTableEntity, Float> data) {
        return data.getValue().getValue().percentageProvenProperty().asObject();
    }

    private ObservableValue<TreeTableEntity.ProofStatus> statusCellFactory(TreeTableColumn.CellDataFeatures<TreeTableEntity, TreeTableEntity.ProofStatus> data) {
        return data.getValue().getValue().proofStatusProperty();
    }
}
