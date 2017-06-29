package edu.kit.iti.algover.browser;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVC;
import javafx.beans.property.*;

/**
 * Created by philipp on 26.06.17.
 */
public class TreeTableEntity {

    public PVC getPvc() {
        return pvc;
    }

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
        DEPENDENT_ON_UNPROVEN
    }

    private final StringProperty name;
    private final FloatProperty percentageProven;
    private final ObjectProperty<ProofStatus> proofStatus;
    private final Kind kind;
    private final DafnyFile location;
    private final PVC pvc; // only != null if this is a pvc node

    public TreeTableEntity(DafnyFile location, PVC pvc, String name, float percentageProven, ProofStatus proofStatus, Kind kind) {
        this.location = location;
        this.pvc = pvc;
        this.name = new SimpleStringProperty(name);
        this.percentageProven = new SimpleFloatProperty(percentageProven);
        this.proofStatus = new SimpleObjectProperty<>(proofStatus);
        this.kind = kind;
    }

    public TreeTableEntity(DafnyFile location, String name, float percentageProven, ProofStatus proofStatus, Kind kind) {
        this(location, null, name, percentageProven, proofStatus, kind);
    }

    public TreeTableEntity(DafnyFile location, PVC pvc, ProofStatus proofStatus) {
        this(location, pvc, pvc.getName(), 0, ProofStatus.UNPROVEN, Kind.PVC);
    }

    public Kind getKind() {
        return kind;
    }

    public DafnyFile getLocation() {
        return location;
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
