/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.Position;
import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.*;

/**
 * Properties for the annotations for the scriptview gutter
 * @author S. Grebing (adapted from A. Weigl PSDBG)
 */
public class GutterAnnotation {


    /**
     * Label text (linenumber)
     */
    private StringProperty text = new SimpleStringProperty();



    /**
     * Boolean flag for marker for command insertion position
     */
    private SimpleBooleanProperty insertMarker = new SimpleBooleanProperty(false, "Marker for insertion");


    /**
     * Associated proof node selector, if existing
     */

    private SimpleObjectProperty<ProofNodeSelector> proofNode = new SimpleObjectProperty<>(null, "Proofnode property");

    private BooleanProperty proofNodeIsSelected = new SimpleBooleanProperty(false, "Proofnode is selected property ");

    private BooleanBinding proofNodeIsSet = proofNode.isNotNull();

    public SimpleBooleanProperty insertMarkerProperty() {
        return insertMarker;
    }

    public void setInsertMarker(boolean insertMarker) {
        this.insertMarker.set(insertMarker);
    }


    public String getText() {
            return text.get();
        }

    public void setText(String text) {
            this.text.set(text);
        }

    public StringProperty textProperty() {
            return text;
        }


    public boolean isInsertMarker() {
        return insertMarker.get();
    }

    public ProofNodeSelector getProofNode() {
        return proofNode.get();
    }

    public SimpleObjectProperty<ProofNodeSelector> proofNodeProperty() {
        return proofNode;
    }

    public void setProofNode(ProofNodeSelector proofNode) {
        this.proofNode.set(proofNode);
    }

    public boolean isProofNodeIsSelected() {
        return proofNodeIsSelected.get();
    }

    public BooleanProperty proofNodeIsSelectedProperty() {
        return proofNodeIsSelected;
    }

    public void setProofNodeIsSelected(boolean proofNodeIsSelected) {
        this.proofNodeIsSelected.set(proofNodeIsSelected);
    }

    public boolean isProofNodeIsSet() {
        return proofNodeIsSet.get();
    }

    public BooleanBinding proofNodeIsSetProperty() {
        return proofNodeIsSet;
    }


}
