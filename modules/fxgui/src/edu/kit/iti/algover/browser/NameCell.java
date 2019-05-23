/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.scene.control.TreeTableCell;
import javafx.scene.input.MouseButton;

/**
 * Created by philipp on 26.06.17.
 */
public class NameCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    private PVCClickEditListener editListener;

    public NameCell() {
        getStyleClass().add("namecell");
    }

    public NameCell(PVCClickEditListener editListener) {
        this.editListener = editListener;
    }

    @Override
    protected void updateItem(TreeTableEntity item, boolean empty) {
        super.updateItem(item, empty);
        if (item != null && !empty) {
            setGraphic(item.accept(TreeTableEntityNameRenderer.INSTANCE));
            setText(item.getText());
            setOnMouseClicked(e -> {
                if(e.getClickCount() >= 2 &&
                        e.getButton() == MouseButton.PRIMARY &&
                        item instanceof PVCEntity) {
                    editListener.onEngageEntity((PVCEntity)item);
                }
            });
        } else {
            setGraphic(null);
            setText(null);
        }
    }
}
