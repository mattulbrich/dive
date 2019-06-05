/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.Quadruple;
import edu.kit.iti.algover.util.SubSelection;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import javafx.css.PseudoClass;
import javafx.scene.control.ListCell;

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

    public FormulaCell(SimpleObjectProperty<TermSelector> selectedTerm,
                       SimpleObjectProperty<TermSelector> selectedReference,
                       ObservableList<Quadruple<TermSelector, String, Integer, String>> allStyles) {
        this.selectedTerm = selectedTerm;
        this.allStyles = allStyles;
        this.selectedReference = selectedReference;
        getStyleClass().add("formula-cell");
    }

    @Override
    protected void updateItem(ViewFormula formula, boolean empty) {
        super.updateItem(formula, empty);
        if (!empty && formula != null) {
            BasicFormulaView formulaView = new BasicFormulaView(formula, selectedTerm, selectedReference, allStyles);
            setGraphic(formulaView);
        } else {
            setGraphic(null);
        }
    }
}
