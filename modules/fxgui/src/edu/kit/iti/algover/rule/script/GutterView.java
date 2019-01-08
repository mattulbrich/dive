package edu.kit.iti.algover.rule.script;

import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIconView;
import javafx.beans.Observable;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;


public class GutterView extends HBox {
    private final SimpleObjectProperty<GutterAnnotation> annotation = new SimpleObjectProperty<>();


    /*private MaterialDesignIconView iconStateHandle = new MaterialDesignIconView(MaterialDesignIcon.CLOSE_CIRCLE_OUTLINE);

    private MaterialDesignIconView iconConditionalBreakPoint = new MaterialDesignIconView(MaterialDesignIcon.CHECK);

    private MaterialDesignIconView iconSkippedSave = new MaterialDesignIconView(MaterialDesignIcon.ALERT);
*/
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
                old.insertMarkerProperty().removeListener(this::update);
                old.proofNodeIsSelectedProperty().removeListener(this::update);
              //  old.textInsertPosProperty().removeListener(this::update);
                lineNumber.textProperty().unbind();
            }
            nv.insertMarkerProperty().addListener(this::update);
            nv.proofNodeIsSelectedProperty().addListener(this::update);
            // nv.textInsertPosProperty().addListener(this::update);
            lineNumber.textProperty().bind(nv.textProperty());

            update(null);
        });
        setAnnotation(ga);
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
