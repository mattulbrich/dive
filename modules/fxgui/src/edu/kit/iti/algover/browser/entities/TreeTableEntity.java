package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import javafx.beans.property.*;

/**
 * Created by philipp on 26.06.17.
 */
public abstract class TreeTableEntity {

    public enum ProofStatus {
        UNPROVEN,
        PROVEN,
        DEPENDENT_ON_UNPROVEN
    }

    private final StringProperty text;
    private final FloatProperty percentageProven;
    private final ObjectProperty<ProofStatus> proofStatus;
    private final DafnyFile location;

    public TreeTableEntity(String text, DafnyFile location) {
        this.text = new SimpleStringProperty(text);
        this.percentageProven = new SimpleFloatProperty(0);
        this.proofStatus = new SimpleObjectProperty<>(ProofStatus.UNPROVEN);
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

    public float getPercentageProven() {
        return percentageProven.get();
    }

    public FloatProperty percentageProvenProperty() {
        return percentageProven;
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
                ", percentageProven=" + percentageProven.get() +
                ", proofStatus=" + proofStatus.get() +
                '}';
    }
}
