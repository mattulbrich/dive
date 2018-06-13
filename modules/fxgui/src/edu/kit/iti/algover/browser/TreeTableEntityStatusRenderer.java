package edu.kit.iti.algover.browser;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
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
        if (entity instanceof PVCEntity) {
            ((PVCEntity) entity).proofStatusProperty().addListener(new ChangeListener<PVCEntity.ProofStatus>() {
                @Override
                public void changed(ObservableValue<? extends PVCEntity.ProofStatus> observable, PVCEntity.ProofStatus oldValue, PVCEntity.ProofStatus newValue) {
                    updateProofStatusIcon(newValue);
                }
            });
        }
    }

    private Void groupingEntity(TreeTableEntity entity) {
        String text = entity.getProvenChildren() + "/" + entity.getNumberChildren();
        cell.setText(text);
        if (entity.getProvenChildren() >= entity.getNumberChildren()) {
            Text icon = GlyphsDude.createIcon(FontAwesomeIcon.CHECK);
            icon.setFill(Color.LIMEGREEN);
            cell.setGraphic(icon);
            cell.setTooltip(new Tooltip("All PVCs proven"));
        } else {
            cell.setTooltip(new Tooltip(
                    entity.getProvenChildren()
                            + " from " + entity.getNumberChildren()
                            + " PVCs proven"));
        }
        return null;
    }

    @Override
    public Void visitPVC(PVCEntity entity) {
        Text statusIcon = GlyphsDude.createIcon(entity.getProofStatus().getIcon());
        statusIcon.setFill(entity.getProofStatus().getFill());

        Text gearIcon = GlyphsDude.createIcon(FontAwesomeIcon.GEAR);
        gearIcon.setFill(Color.DARKGREY);
        gearButton = new Button("Edit", gearIcon);
        gearButton.getStyleClass().add("undecorated-button");
        gearButton.setTooltip(new Tooltip("Edit or start Proof"));
        gearButton.setOnAction(event -> {
            if (engagedListener != null) {
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

    public void updateProofStatusIcon(PVCEntity.ProofStatus proofStatus) {
        Text statusIcon = GlyphsDude.createIcon(proofStatus.getIcon());
        statusIcon.setFill(proofStatus.getFill());
        HBox box = new HBox(statusIcon, gearButton);
        box.setSpacing(10);
        box.setAlignment(Pos.CENTER);
        cell.setGraphic(box);
    }
}
