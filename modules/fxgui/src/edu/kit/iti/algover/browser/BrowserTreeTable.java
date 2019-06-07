/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;


import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.*;

/**
 * Created by Philipp on 15.06.2017.
 */
public class BrowserTreeTable extends TreeTableView<TreeTableEntity> {

    private TreeTableColumn<TreeTableEntity, TreeTableEntity> nameColumn;
    private TreeTableColumn<TreeTableEntity, TreeTableEntity> statusColumn;
    private final PVCClickEditListener editListener;

    private ContextMenu rootContextMenu;

    @SuppressWarnings("unchecked")
    public BrowserTreeTable(PVCClickEditListener editListener) {
        this.editListener = editListener;
        this.nameColumn = new TreeTableColumn<>("name");
        this.statusColumn = new TreeTableColumn<>("status");

        getStyleClass().addAll("browser");

        nameColumn.setCellValueFactory(this::nameCellFactory);
        statusColumn.setCellValueFactory(this::statusCellFactory);

        nameColumn.setCellFactory(this::nameCellRenderer);
        statusColumn.setCellFactory(this::statusCellRenderer);

        setColumnResizePolicy(CONSTRAINED_RESIZE_POLICY);

        statusColumn.setMaxWidth(120);
        statusColumn.setPrefWidth(100);
        statusColumn.setMinWidth(80);

        nameColumn.setMinWidth(100);

        super.getColumns().setAll(nameColumn, statusColumn);
        this.rootContextMenu = new ContextMenu();
        this.setContextMenu(this.rootContextMenu);
    }

    private TreeTableCell<TreeTableEntity, TreeTableEntity> statusCellRenderer(TreeTableColumn<TreeTableEntity, TreeTableEntity> column) {
        return new StatusCell(editListener);
    }

    private TreeTableCell<TreeTableEntity, TreeTableEntity> nameCellRenderer(TreeTableColumn<TreeTableEntity, TreeTableEntity> column) {
        return new NameCell(editListener);
    }

    private ObservableValue<TreeTableEntity> nameCellFactory(TreeTableColumn.CellDataFeatures<TreeTableEntity, TreeTableEntity> data) {
        return data.getValue().valueProperty();
    }

    private ObservableValue<TreeTableEntity> statusCellFactory(TreeTableColumn.CellDataFeatures<TreeTableEntity, TreeTableEntity> data) {
        return data.getValue().valueProperty();
    }
}
