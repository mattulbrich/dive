/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Quadruple;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import org.fxmisc.flowless.VirtualizedScrollPane;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 22.07.2017.
 * updated by JonasKlamroth on 28.5.19
 * updated by S.Grebing on 12.06.19
 *
 * This Class is basically a wrapper to provide {@link BasicFormulaView}s as BorderPanes for the VBoxes in the
 * {@link SequentController} containing meta information about the formulas
 */
public class FormulaCell extends BorderPane {
    SimpleObjectProperty<TermSelector> selectedTerm;
    SimpleObjectProperty<TermSelector> selectedReference;
    ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles;
    ImmutableList<String> label = ImmutableList.nil();
    private Set<TermSelector> highlightSet = new HashSet<>();

    private Tooltip tooltip = new Tooltip();

    private SimpleBooleanProperty showLabels;

    private SimpleIntegerProperty fontsize;


    public FormulaCell(SimpleObjectProperty<TermSelector> selectedTerm,
                       SimpleObjectProperty<TermSelector> selectedReference,
                       ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles,
                       ViewFormula formula,
                       SimpleBooleanProperty showLabelsInView, SimpleIntegerProperty fontsize) {
        this.selectedTerm = selectedTerm;
        this.allStyles = allStyles;
        this.selectedReference = selectedReference;
        this.showLabels = showLabelsInView;
        this.fontsize = fontsize;

        this.setPadding(new Insets(5,10,5,10));
        getStyleClass().add("formula-cell");

        this.setBorder(new Border(new BorderStroke(Color.LIGHTGRAY,
            BorderStrokeStyle.SOLID, CornerRadii.EMPTY, BorderWidths.DEFAULT)));
        this.setBackground(new Background(new BackgroundFill(Color.WHITE, null, null)));

        // set a non-null side object to force repaint on resize.
        Rectangle rectangle = new Rectangle(0,0);
        this.setRight(rectangle);

        updateItem(formula);
        showLabels(showLabelsInView.get());
        showLabelsInView.addListener((observable, oldValue, newValue) -> {
            showLabels(newValue);
        });

    }

    protected void updateItem(ViewFormula formula) {
       if (formula != null) {
           //selectors to highlight
           Set<TermSelector> filterAccToIndexInSeq = highlightSet
                   .stream()
                   .filter(termSelector ->
                          termSelector.getToplevelSelector().getTermNo() == formula.getIndexInSequent())
                   .collect(Collectors.toSet());
           BasicFormulaView formulaView = new BasicFormulaView(formula, selectedTerm, selectedReference, allStyles, filterAccToIndexInSeq, fontsize);
           this.label = formula.getLabels();
           //VirtualizedScrollPane<BasicFormulaView> sp = new VirtualizedScrollPane<>(formulaView);
           //setCenter(sp);

           this.minWidthProperty().bind(formulaView.prefWidthProperty());

           setCenter(formulaView);
           createTooltip();

        } else {
            getChildren().clear();
        }
    }

    private void createTooltip() {
        StringBuilder labelString = new StringBuilder();
        this.label.forEach(s -> {
            labelString.append(s + "\n");
        });
        tooltip.setText(labelString.toString());
        Tooltip.install(this, tooltip);
    }


     public void setSelectorsToHighlight(Set<TermSelector> selectorsToHighlight) {
        this.highlightSet = selectorsToHighlight;
    }

    public void showLabels(boolean show){
        if(show && !label.isEmpty()){
            StringBuilder labelString = new StringBuilder();
            this.label.forEach(s -> {
                labelString.append(s + "\n");
            });
            HBox hbox = new HBox();
            List<Label> values = buildAndStyleLabel();
            hbox.getChildren().addAll(values);
            hbox.setAlignment(Pos.BOTTOM_RIGHT);
            //value.setContextMenu(new ContextMenu(new MenuItem("test")));
            this.setBottom(hbox);
            //Rectangle rectangle = new Rectangle(20, 20);
            //rectangle.setFill(Color.BLUE);
            //this.setRight(rectangle);
        } else {
            this.setBottom(null);
        }
    }

    //TODO externalize
    private List<Label> buildAndStyleLabel() {
        List<Label> labelViews = new ArrayList<Label>();
        for(String l : this.label){
            Label view;
            switch (l){
                case "PreCond":
                    view = new Label("Pre");
                    view.setStyle("-fx-text-fill: #62aaff");
                    //this.setStyle("-fx-background-color:  #62aaff");
                    labelViews.add(view);
                    break;
                case "Assertion":
                    view = new Label("Assertion");
                    view.setStyle("-fx-text-fill: #803480");
                    labelViews.add(view);
                    break;
                case "PostCond":
                    view = new Label("Post");
                    view.setStyle("-fx-text-fill: #ffec46");
                    labelViews.add(view);
                    break;
                case "Assumption":
                    view = new Label(l);
                    view.setStyle("-fx-text-fill: #ff8ca1");
                    labelViews.add(view);
                    break;
                case "PathCond":
                    view = new Label("Pathcondition");
                    view.setStyle("-fx-text-fill: #256280");
                    labelViews.add(view);
                    break;

                default:
                    view = new Label(l);
                    view.setStyle("-fx-text-fill: GRAY");
                    labelViews.add(view);

            }
        }
        return labelViews;
    }
}
