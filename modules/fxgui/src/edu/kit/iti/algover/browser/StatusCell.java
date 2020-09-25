/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.geometry.Pos;
import javafx.scene.control.TreeTableCell;

/**
 * Created by Philipp on 14.08.2017.
 */
public class StatusCell extends TreeTableCell<TreeTableEntity, TreeTableEntity> {

    private final PVCClickEditListener engagedListener;

    private final ChangeListener<Number> repaintListener =
            (x,y,z) -> updateItem(getItem(), false);

    private final ChangeListener<PVCEntity.ProofStatus> repaintListenerPVC =
            (state, old, nu) -> updateItem(getItem(), false);

    public StatusCell(PVCClickEditListener engagedListener) {
        this.engagedListener = engagedListener;
        getStyleClass().add("status-cell");
        setAlignment(Pos.CENTER);

        itemProperty().addListener((obs, old, nu) -> {
            if (old != null) {
                old.provenChildrenProperty().removeListener(repaintListener);
            }
            if (nu != null) {
                nu.provenChildrenProperty().addListener(repaintListener);
            }

            if (old instanceof PVCEntity) {
                ((PVCEntity) old).proofStatusProperty().removeListener(repaintListenerPVC);
            }

            if (nu instanceof PVCEntity) {
                ((PVCEntity) nu).proofStatusProperty().addListener(repaintListenerPVC);
            }


        });
    }

    @Override
    protected void updateItem(TreeTableEntity item, boolean empty) {
        super.updateItem(item, empty);
        Platform.runLater(() -> {
            setText(null);
            if (item != null && !empty) {
                TreeTableEntityStatusRenderer renderer = new TreeTableEntityStatusRenderer(this);
                renderer.applyRendering(item, engagedListener);
            } else {
                setGraphic(null);
                setTooltip(null);
            }
        });
    }

}
