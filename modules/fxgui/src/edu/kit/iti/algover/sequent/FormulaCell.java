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
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;

import java.util.HashSet;
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


    public FormulaCell(SimpleObjectProperty<TermSelector> selectedTerm,
                       SimpleObjectProperty<TermSelector> selectedReference,
                       ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles,
                       ViewFormula formula) {

        this.selectedTerm = selectedTerm;
        this.allStyles = allStyles;
        this.selectedReference = selectedReference;
        this.setPadding(new Insets(10,10,10,10));
        getStyleClass().add("formula-cell");
        this.setBorder(new Border(new BorderStroke(Color.BLACK,
            BorderStrokeStyle.SOLID, CornerRadii.EMPTY, BorderWidths.DEFAULT)));
        updateItem(formula);
    }

    protected void updateItem(ViewFormula formula) {
       if (formula != null) {
            //selectors to highlight
            Set<TermSelector> filterAccToIndexInSeq = highlightSet
                    .stream()
                    .filter(termSelector ->
                            termSelector.getToplevelSelector().getTermNo() == formula.getIndexInSequent())
                    .collect(Collectors.toSet());
            BasicFormulaView formulaView = new BasicFormulaView(formula, selectedTerm, selectedReference, allStyles, filterAccToIndexInSeq);
            this.label = formula.getLabels();
            StringBuilder t = new StringBuilder();
            this.label.forEach(s -> {
               t.append(s+"\n");
            });
            tooltip.setText(t.toString());
            setCenter(formulaView);
            Tooltip.install(this, tooltip);
        } else {
            getChildren().clear();
        }
    }

     public void setSelectorsToHighlight(Set<TermSelector> selectorsToHighlight) {
        this.highlightSet = selectorsToHighlight;
    }
}
