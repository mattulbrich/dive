/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.util.Quadruple;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ListCell;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 22.07.2017.
 * updated by JonasKlamroth on 28.5.19
 *
 * This Class is basically a wrapper to provide {@link BasicFormulaView}s as cells to the ListViews in the
 * {@link SequentController}
 */
public class FormulaCell extends ListCell<ViewFormula> {
    SimpleObjectProperty<TermSelector> selectedTerm;
    SimpleObjectProperty<TermSelector> selectedReference;
    ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles;
    private Set<TermSelector> highlightSet = new HashSet<>();

    public FormulaCell(SimpleObjectProperty<TermSelector> selectedTerm,
                       SimpleObjectProperty<TermSelector> selectedReference,
                       ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles
                       ) {
        this.selectedTerm = selectedTerm;
        this.allStyles = allStyles;
        this.selectedReference = selectedReference;
        getStyleClass().add("formula-cell");

    }

    @Override
    protected void updateItem(ViewFormula formula, boolean empty) {
        super.updateItem(formula, empty);
        if (!empty && formula != null) {
            //selectors to highlight
            Set<TermSelector> filterAccToIndexInSeq = highlightSet
                    .stream()
                    .filter(termSelector ->
                            termSelector.getToplevelSelector().getTermNo() == formula.getIndexInSequent())
                    .collect(Collectors.toSet());
            BasicFormulaView formulaView = new BasicFormulaView(formula, selectedTerm, selectedReference, allStyles, filterAccToIndexInSeq);
            setGraphic(formulaView);
        } else {
            setGraphic(null);
        }
    }

     public void setSelectorsToHighlight(Set<TermSelector> selectorsToHighlight) {
        this.highlightSet = selectorsToHighlight;
    }
}
