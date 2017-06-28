package edu.kit.iti.algover.browser;

import javafx.beans.property.*;

/**
 * Created by philipp on 26.06.17.
 */
public class TreeTableEntity {

    public enum Kind {
        METHOD,
        FUNCTION,
        CLASS,
        MODULE,
        PVC,
        OTHER // Does not render specially. E.g. the root node or file nodes
    }

    public enum ProofStatus {
        UNPROVEN,
        PROVEN,
        DEPENDENT_ON_UNPROVEN;
    }

    private final StringProperty name;
    private final FloatProperty percentageProven;
    private final ObjectProperty<ProofStatus> proofStatus;
    private final Kind kind;

    public TreeTableEntity(String name, float percentageProven, ProofStatus proofStatus, Kind kind) {
        this.name = new SimpleStringProperty(name);
        this.percentageProven = new SimpleFloatProperty(percentageProven);
        this.proofStatus = new SimpleObjectProperty<>(proofStatus);
        this.kind = kind;
    }

    public Kind getKind() {
        return kind;
    }

    public String getName() {
        return name.get();
    }

    public StringProperty nameProperty() {
        return name;
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
                "name=" + name.get() +
                ", percentageProven=" + percentageProven.get() +
                ", proofStatus=" + proofStatus.get() +
                ", kind=" + kind +
                '}';
    }
}
