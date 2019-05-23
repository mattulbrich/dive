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
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;


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

    public GutterView(GutterAnnotation ga) {

        annotation.addListener((o, old, nv) -> {

            if (old != null) {
                lineNumber.textProperty().unbind();
            }
            lineNumber.textProperty().bind(nv.textProperty());

            update(null);
        });
        ga.insertMarkerProperty().addListener(this::update);
        ga.proofNodeIsSelectedProperty().addListener(this::update);
        ga.proofNodeIsSelectedProperty().addListener((observable, oldValue, newValue) -> {
         //   System.out.println("selection changed");
            this.update(observable);
        });
        setAnnotation(ga);
        update(null);

    }

    public void update(Observable o) {

        getChildren().setAll(lineNumber);
        if(getAnnotation().isProofNodeIsSet()){
            if(getAnnotation().isProofNodeIsSelected())
                getChildren().add(iconProofNodeSelected);
            else
                getChildren().add(iconProofNodeUnSelected);
        }
        else {
            addPlaceholder();
        }
        if(getAnnotation().isInsertMarker())
            getChildren().add(iconProofCommandPosition);
        else
            addPlaceholder();

    }

    public GutterAnnotation getAnnotation() {
        return annotation.get();
    }

    public void setAnnotation(GutterAnnotation annotation) {
        this.annotation.set(annotation);
    }

    private void addPlaceholder() {
        Label lbl = new Label();
        lbl.setMinWidth(12);
        lbl.setMinHeight(12);
        getChildren().add(lbl);
    }

    public SimpleObjectProperty<GutterAnnotation> annotationProperty() {
        return annotation;
    }
}
