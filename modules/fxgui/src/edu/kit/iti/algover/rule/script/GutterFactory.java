/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import javafx.beans.Observable;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleListProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.input.MouseButton;
import javafx.scene.layout.Background;
import javafx.scene.layout.BackgroundFill;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;
import javafx.scene.text.Font;
import javafx.scene.text.FontPosture;
import javafx.util.Callback;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.LineNumberFactory;
import org.reactfx.collection.LiveList;
import org.reactfx.value.Val;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.function.IntFunction;

/**
 * Factory for the gutter in the script view
 * @author A.Weigl (PSDBG)
 * @author S. Grebing (adapted)
 */
public class GutterFactory implements IntFunction<Node> {

    /**
     * Background Color
     */
    private final Background defaultBackground =
            new Background(new BackgroundFill(Color.web("#ddd"), null, null));

    private final Val<Integer> nParagraphs;

    private Insets defaultInsets = new Insets(0.0, 5.0, 0.0, 5.0);

    private Paint defaultTextFill = Color.web("#666");

    private Font defaultFont = Font.font("monospace", FontPosture.ITALIC, 13);

    private ObservableList<GutterAnnotation> lineAnnotations =
            new SimpleListProperty<>(FXCollections.observableArrayList());

    private ScriptView codeArea;

    private SimpleIntegerProperty fontsize = new SimpleIntegerProperty(12);

    public GutterFactory(ScriptView codeArea, SimpleIntegerProperty fontsize) {
        this.codeArea = codeArea;
        this.fontsize.bind(fontsize);
        nParagraphs = LiveList.sizeOf(codeArea.getParagraphs());
        for (int i = 0; i < 100; i++) {

            GutterAnnotation e = new GutterAnnotation();
            if(i==0 && nParagraphs.getValue() == 1){
                e.setInsertMarker(true);
            }
            lineAnnotations.add(e);
        }

        // Update the gutter.
        // If a line is deleted, delete also the image entry for this line
        nParagraphs.addInvalidationObserver((n) -> {
            int diff = lineAnnotations.size() - n;
            if (diff > 0) {
                lineAnnotations.remove(n, lineAnnotations.size());
            }
        });

        this.fontsize.addListener((observable, oldValue, newValue) -> {
            System.out.println("fontsize = " + fontsize);
        });
        /*lineAnnotations.addListener(new ListChangeListener<GutterAnnotation>() {
            @Override
            public void onChanged(Change<? extends GutterAnnotation> c) {
                
                System.out.println("list changed");
                lineAnnotations.forEach(gutterAnnotation -> {
                    System.out.println("gutterAnnotation.Text() = " + gutterAnnotation.getText());
                    System.out.println("gutterAnnotation.isInsertMarker() = " + gutterAnnotation.isInsertMarker());
                });
                list.forEach(gutterView -> {
                    System.out.println("gutterView.getLineNumber() = " + gutterView.getLineNumber());
                    System.out.println("gutterViewM = " + gutterView.getAnnotation().isInsertMarker()+" "+gutterView.getAnnotation().getText());

                });
            }
        });*/


    }

    @Override
    public Node apply(int idx) {
        if (idx == -1) return new Label("idx is -1!"); //TODO weigl debug
        Val<String> formatted = nParagraphs.map(n -> format(idx + 1, n));
        GutterAnnotation model = getLineAnnotation(idx);
        model.fontsizeProperty().bind(this.fontsize);
        GutterView hbox = new GutterView(model);
        model.textProperty().bind(formatted);
        //process clicking on the gutter by setting the selection in the model
        hbox.setOnMouseClicked((mevent) -> {
            mevent.consume();
            if (mevent.getButton() == MouseButton.PRIMARY) {
                if (hbox.getAnnotation().isProofNodeIsSet()) {
                    // Integer lnr = Integer.parseInt(hbox.getLineNumber().getText().replaceAll(" ", ""));
                    //codeArea.displaceCaret(lnr);
                    hbox.getAnnotation().setProofNodeIsSelected(true);
                }
            }
        });

        hbox.getLineNumber().setFont(defaultFont);
        hbox.setBackground(defaultBackground);
        hbox.getLineNumber().setTextFill(defaultTextFill);
        hbox.setPadding(defaultInsets);
        hbox.getStyleClass().add("lineno");
        hbox.setStyle("-fx-cursor: hand;"+"-fx-font-size: "+this.fontsize.get()+"pt;");
        return hbox;
    }

    private String format(int x, int max) {
        int digits = (int) Math.floor(Math.log10(max)) + 1;
        return String.format("%" + digits + "d", x);
    }

    public GutterAnnotation getLineAnnotation(int idx) {
        if (lineAnnotations.size() <= idx) {
            for (int i = lineAnnotations.size(); i < idx + 1; i++) {
                lineAnnotations.add(new GutterAnnotation());
            }
        }
        return lineAnnotations.get(idx);
    }

    public ObservableList<GutterAnnotation> getAnnotations() {
        return this.lineAnnotations;
    }

}
