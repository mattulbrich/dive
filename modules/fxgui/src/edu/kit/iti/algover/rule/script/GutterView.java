package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIconView;
import javafx.beans.Observable;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;


public class GutterView extends HBox {
    private final SimpleObjectProperty<GutterAnnotation> annotation = new SimpleObjectProperty<>();


    private MaterialDesignIconView iconBreakPoint = new MaterialDesignIconView(MaterialDesignIcon.STOP);

    private MaterialDesignIconView iconConditionalBreakPoint = new MaterialDesignIconView(MaterialDesignIcon.CHECK);

    private MaterialDesignIconView iconSkippedSave = new MaterialDesignIconView(MaterialDesignIcon.ALERT);

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
                old.breakpointProperty().removeListener(this::update);
                old.breakpointConditionProperty().removeListener(this::update);
                lineNumber.textProperty().unbind();
            }

            nv.breakpointProperty().addListener(this::update);
            nv.breakpointProperty().addListener(this::update);
            nv.conditionalProperty().addListener(this::update);

            lineNumber.textProperty().bind(nv.textProperty());

            update(null);
        });
        setAnnotation(ga);
    }

    public void update(Observable o) {
        getChildren().setAll(lineNumber);
        addPlaceholder();
        if (getAnnotation().isAlert()) getChildren().add(iconSkippedSave);
        else addPlaceholder();
        if (getAnnotation().isBreakpoint())
            getChildren().add(getAnnotation().getConditional()
                    ? iconConditionalBreakPoint
                    : iconBreakPoint);
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
