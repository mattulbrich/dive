package edu.kit.iti.algover.browser.entities;

import de.jensd.fx.glyphs.GlyphIcons;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import javafx.beans.property.*;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.scene.text.Font;

/**
 * Created by philipp on 26.06.17.
 */
public abstract class TreeTableEntity {

    public enum ProofStatus {
        UNPROVEN(
            FontAwesomeIcon.EXCLAMATION,
            Color.RED,
            "No proof for this PVC"),
        PROVEN(
            FontAwesomeIcon.CHECK,
            Color.GREEN,
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

    private final StringProperty text;
    private final ObjectProperty<ProofStatus> proofStatus;
    private final DafnyFile location;

    public TreeTableEntity(String text, DafnyFile location) {
        this.text = new SimpleStringProperty(text);
        this.proofStatus = new SimpleObjectProperty<>(ProofStatus.values()[(int)(Math.random()*3)]);
        this.location = location;
    }

    public abstract <T> T accept(TreeTableEntityVisitor<T> visitor);

    public DafnyFile getLocation() {
        return location;
    }

    public String getText() {
        return text.get();
    }

    public StringProperty textProperty() {
        return text;
    }

    public ProofStatus getProofStatus() {
        return proofStatus.get();
    }

    public ObjectProperty<ProofStatus> proofStatusProperty() {
        return proofStatus;
    }

    @Override
    public String toString() {
        return "TreeTableEntity{" +
                "name=" + text.get() +
                ", proofStatus=" + proofStatus.get() +
                '}';
    }
}
