/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIconView;
import javafx.beans.Observable;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;

import java.util.Arrays;

/**
 * GutterView in the Script
 * @author A.Weigl, S.Grebing
 */
public class GutterView extends HBox {
    private final SimpleObjectProperty<GutterAnnotation> annotation = new SimpleObjectProperty<>();

    private MaterialDesignIconView iconProofCommandPosition = new MaterialDesignIconView(MaterialDesignIcon.FORMAT_TEXTDIRECTION_L_TO_R);

    private MaterialDesignIconView iconProofNodeSelected = new MaterialDesignIconView(MaterialDesignIcon.ADJUST);

    private MaterialDesignIconView iconProofNodeUnSelected = new MaterialDesignIconView(MaterialDesignIcon.PANORAMA_FISHEYE);

    public Label getLineNumber() {
        return lineNumber;
    }

    public void setLineNumber(Label lineNumber) {
        this.lineNumber = lineNumber;
    }

    private Label lineNumber = new Label("not set");

    private Node[] gutter = new Node[3];

    public GutterView(GutterAnnotation ga) {
        gutter[0] = lineNumber;
        if(ga.isProofNodeIsSet()) {
            if(ga.isProofNodeIsSelected())
                gutter[1] = iconProofNodeSelected;
            else
                gutter[1] =iconProofNodeUnSelected;
        } else {
            gutter[1] = placeholder();
        }
        if(ga.isInsertMarker()){
            gutter[2] = iconProofCommandPosition;
        } else {
            gutter[2] = placeholder();
        }
        annotation.addListener((o, old, nv) -> {

            if (old != null) {
                lineNumber.textProperty().unbind();
            }
            lineNumber.textProperty().bind(nv.textProperty());

            update(null);
        });
        ga.proofNodeIsSetProperty().addListener(this::updateProofNode);
        ga.insertMarkerProperty().addListener(this::updateMarker);
        ga.proofNodeIsSelectedProperty().addListener(this::updateProofNodeSelection);
        ga.proofNodeIsReferencedProperty().addListener(this::updateReferences);
        ga.proofNodeIsSelectedProperty().addListener((observable, oldValue, newValue) -> {
            updateProofNodeSelection(observable);
        });
        setAnnotation(ga);

        update(null);
    }

    private void updateMarker(Observable o) {
        if(getAnnotation().isInsertMarker()){
            gutter[2] = iconProofCommandPosition;
        } else {
            gutter[2] = placeholder();
        }
        updateProofNodeSelection(o);
        update(o);
    }

    private void updateProofNodeSelection(Observable observable) {
        if(getAnnotation().isProofNodeIsSet()) {
            Paint fill = ((MaterialDesignIconView) gutter[1]).getFill();
            if (getAnnotation().isProofNodeIsSelected()) {
                gutter[1] = iconProofNodeSelected;
            } else {
                gutter[1] = iconProofNodeUnSelected;
            }

        } else {
            gutter[1] = placeholder();
        }
        updateReferences(observable);
        update(observable);
    }

    private void updateProofNode(Observable o) {
        if(getAnnotation().isProofNodeIsSet()){
            gutter[1] = iconProofNodeUnSelected;

        } else {
            gutter[1] = placeholder();
        }
        updateProofNodeSelection(o);
        update(o);
    }

    private void updateReferences(Observable observable) {
        if(getAnnotation().isProofNodeIsSet()) {
            MaterialDesignIconView node = (MaterialDesignIconView) gutter[1];
            if (getAnnotation().proofNodeIsReferenced()) {
                node.setFill(Color.PURPLE);
                gutter[1] = node;
            } else {
                node.setFill(Color.BLACK);
            }
        } else {
            gutter[1] = placeholder();
        }
        update(observable);
    }

    /**
     * Update the GutterView with the components stored in the Gutter Array
     * @param o
     */
    public void update(Observable o){
        getChildren().setAll(gutter[0]);
        getChildren().add(gutter[1]);
        getChildren().add(gutter[2]);
    }


    public GutterAnnotation getAnnotation() {
        return annotation.get();
    }

    public void setAnnotation(GutterAnnotation annotation) {
        this.annotation.set(annotation);
    }

    private Label placeholder(){
        Label lbl = new Label();
        lbl.setMinWidth(12);
        lbl.setMinHeight(12);
        return lbl;
    }
    public SimpleObjectProperty<GutterAnnotation> annotationProperty() {
        return annotation;
    }

}
