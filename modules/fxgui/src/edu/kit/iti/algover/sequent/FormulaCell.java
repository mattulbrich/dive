package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.beans.property.SimpleObjectProperty;
import javafx.css.PseudoClass;
import javafx.scene.control.ListCell;

/**
 * Created by Philipp on 22.07.2017.
 */
public class FormulaCell extends ListCell<ViewFormula> {
    SimpleObjectProperty<TermSelector> selectedTerm;

    public FormulaCell(SimpleObjectProperty<TermSelector> selectedTerm) {
        this.selectedTerm = selectedTerm;
        getStyleClass().add("formula-cell");
    }

    @Override
    protected void updateItem(ViewFormula formula, boolean empty) {
        super.updateItem(formula, empty);
        if (!empty && formula != null) {
            BasicFormulaView formulaView = new BasicFormulaView(formula, selectedTerm);
            setGraphic(formulaView);
        } else {
            setGraphic(null);
        }
    }
}
