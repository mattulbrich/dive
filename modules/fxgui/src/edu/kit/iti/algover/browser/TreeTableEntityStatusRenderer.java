/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.browser.entities.*;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.HBox;
import javafx.scene.paint.Color;
import javafx.scene.text.Text;

public class TreeTableEntityStatusRenderer implements TreeTableEntityVisitor<Void> {

    private final StatusCell cell;
    private PVCClickEditListener engagedListener;
    private Button gearButton;

    public TreeTableEntityStatusRenderer(StatusCell cell) {
        this.cell = cell;
    }

    public void applyRendering(TreeTableEntity entity, PVCClickEditListener engagedListener) {
        entity.accept(this);
        this.engagedListener = engagedListener;
    }

    private Void groupingEntity(TreeTableEntity entity) {
        String text = entity.getProvenChildren() + "/" + entity.getNumberChildren();
        cell.setText(text);
        if (entity.getProvenChildren() >= entity.getNumberChildren()) {
            Text icon = FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.CHECK);
            icon.setFill(Color.LIMEGREEN);
            cell.setGraphic(icon);
            cell.setTooltip(new Tooltip("All PVCs proven"));
        } else {
            Text icon = FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.EXCLAMATION);
            icon.setFill(Color.RED);
            cell.setGraphic(icon);
            cell.setTooltip(new Tooltip(
                    entity.getProvenChildren()
                            + " from " + entity.getNumberChildren()
                            + " PVCs proven"));
        }
        return null;
    }

    public void updateProofStatusIcon(PVCEntity.ProofStatus proofStatus) {
        Text statusIcon = FontAwesomeIconFactory.get().createIcon(proofStatus.getIcon());
        statusIcon.setFill(proofStatus.getFill());
        HBox box = new HBox(statusIcon, gearButton);
        box.setSpacing(10);
        box.setAlignment(Pos.CENTER);
        cell.setGraphic(box);
    }

    @Override
    public Void visitMethod(MethodEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Void visitFile(FileEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Void visitClass(ClassEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Void visitPVCGroup(PVCGroupEntity group) {
        return groupingEntity(group);
    }

    @Override
    public Void visitOther(OtherEntity entity) {
        return groupingEntity(entity);
    }

    @Override
    public Void visitFunction(FunctionEntity functionEntity) {
        return groupingEntity(functionEntity);
    }

    @Override
    public Void visitPVC(PVCEntity entity) {
        Text statusIcon = FontAwesomeIconFactory.get().createIcon(entity.getProofStatus().getIcon());
        statusIcon.setFill(entity.getProofStatus().getFill());

        Text gearIcon = FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.GEAR);
        gearIcon.setFill(Color.DARKGREY);
        gearButton = new Button("Edit", gearIcon);
        gearButton.getStyleClass().add("undecorated-button");
        gearButton.setTooltip(new Tooltip("Edit or start Proof"));
        gearButton.setOnAction(event -> {
            if (engagedListener != null) {
                PropertyManager.getInstance().currentPVC.setValue(entity.accept(new PVCGetterVisitor()));
                engagedListener.onEngageEntity(entity);
            }
        });

        HBox box = new HBox(statusIcon, gearButton);
        box.setSpacing(10);
        box.setAlignment(Pos.CENTER);
        Tooltip.install(box, new Tooltip(entity.getProofStatus().getTooltip()));

        cell.setText("");
        cell.setGraphic(box);
        return null;
    }
}
