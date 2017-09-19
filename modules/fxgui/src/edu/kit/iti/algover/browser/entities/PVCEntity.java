package edu.kit.iti.algover.browser.entities;

import de.jensd.fx.glyphs.GlyphIcons;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVC;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;

import java.util.Collections;

/**
 * Created by philipp on 12.07.17.
 */
public class PVCEntity extends TreeTableEntity {

    public enum ProofStatus {
        UNPROVEN(
                FontAwesomeIcon.EXCLAMATION,
                Color.RED,
                "No proof for this PVC"),
        PROVEN(
                FontAwesomeIcon.CHECK,
                Color.LIMEGREEN,
                "Has been proven"),
        DEPENDENT_ON_UNPROVEN(
                FontAwesomeIcon.WARNING,
                Color.ORANGE,
                "Proof with unproven dependencies exists");

        ProofStatus(GlyphIcons icon, Paint fill, String tooltip) {
            this.icon = icon;
            this.fill = fill;
            this.tooltip = tooltip;
        }

        private final GlyphIcons icon;
        private final Paint fill;
        private final String tooltip;

        public GlyphIcons getIcon() {
            return icon;
        }

        public Paint getFill() {
            return fill;
        }

        public String getTooltip() {
            return tooltip;
        }
    }

    private final PVC pvc;
    private final ObjectProperty<ProofStatus> proofStatus;

    public PVCEntity(PVC pvc, DafnyFile location) {
        super(pvc.getName(), location, Collections.emptyList());
        this.pvc = pvc;
        this.proofStatus = new SimpleObjectProperty<>(ProofStatus.values()[(int) (Math.random() * 3)]);
        if (proofStatus.get() == ProofStatus.PROVEN) {
            provenChildrenProperty().set(1);
        }
        numberChildrenProperty().set(1);
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitPVC(this);
    }

    public PVC getPVC() {
        return pvc;
    }

    public ProofStatus getProofStatus() {
        return proofStatus.get();
    }

    public ObjectProperty<ProofStatus> proofStatusProperty() {
        return proofStatus;
    }

    public void setProven() {
        proofStatus.set(ProofStatus.PROVEN);
        numberChildrenProperty().set(1);
    }

}
