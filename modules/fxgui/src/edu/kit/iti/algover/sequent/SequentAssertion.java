package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.proof.ProofFormula;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * Created by philipp on 12.07.17.
 */
public class SequentAssertion {

    private final StringProperty text;

    public SequentAssertion(ProofFormula proofFormula) {
        this.text = new SimpleStringProperty(proofFormula.getTerm().toString());
    }

    public String getText() {
        return text.get();
    }

    public StringProperty textProperty() {
        return text;
    }

    public String toString() {
        return text.get();
    }
}
