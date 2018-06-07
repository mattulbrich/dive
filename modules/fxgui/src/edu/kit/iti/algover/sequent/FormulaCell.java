package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.css.PseudoClass;
import javafx.scene.control.ListCell;

import java.util.List;

/**
 * Created by Philipp on 22.07.2017.
 */
public class FormulaCell extends ListCell<TopLevelFormula> {

    private static final PseudoClass PC_ADDED = PseudoClass.getPseudoClass("formula-added");
    private static final PseudoClass PC_DELETED = PseudoClass.getPseudoClass("formula-deleted");
    private static final PseudoClass PC_MODIFIED = PseudoClass.getPseudoClass("formula-modified");

    private final TermSelector.SequentPolarity polarity;
    private final SubSelection<TermSelector> referenceSelection;
    private final SubSelection<TermSelector> lastClickedTerm;
    private final SubSelection<AnnotatedString.TermElement> mouseOverTerm;

    public FormulaCell(TermSelector.SequentPolarity polarity,
                       SubSelection<TermSelector> referenceSelection,
                       SubSelection<TermSelector> lastClickedTerm,
                       SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        getStyleClass().add("formula-cell");
        this.polarity = polarity;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;
        this.mouseOverTerm = mouseOverTerm;
    }

    @Override
    protected void updateItem(TopLevelFormula formula, boolean empty) {
        super.updateItem(formula, empty);
        if (!empty && formula != null) {
            setPseudoClasses(formula);
            BasicFormulaView formulaView = createRespectiveFormulaView(formula);
            setGraphic(formulaView);
        } else {
            setPseudoClasses(null);
            setGraphic(null);
        }
    }

    protected BasicFormulaView createRespectiveFormulaView(TopLevelFormula formula) {
        return formula.accept(new TopLevelFormulaVisitor<BasicFormulaView>() {
            @Override
            public BasicFormulaView visitOriginalFormula(OriginalFormula formula) {
                return new OriginalFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm);
            }

            @Override
            public BasicFormulaView visitAddedOrDeletedFormula(AddedOrDeletedFormula formula) {
                return new BasicFormulaView(formula, mouseOverTerm);
            }

            @Override
            public BasicFormulaView visitModifiedFormula(ModifiedFormula formula) {
                return new ModifiedFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm);
            }
        });
    }

    protected void setPseudoClasses(TopLevelFormula formula) {
        if (formula == null) {
            FormulaCell.this.pseudoClassStateChanged(PC_ADDED, false);
            FormulaCell.this.pseudoClassStateChanged(PC_DELETED, false);
            FormulaCell.this.pseudoClassStateChanged(PC_MODIFIED, false);
            return;
        }
        formula.accept(new TopLevelFormulaVisitor<Void>() {
            @Override
            public Void visitOriginalFormula(OriginalFormula formula) {
                FormulaCell.this.pseudoClassStateChanged(PC_ADDED, false);
                FormulaCell.this.pseudoClassStateChanged(PC_DELETED, false);
                FormulaCell.this.pseudoClassStateChanged(PC_MODIFIED, false);
                return null;
            }

            @Override
            public Void visitAddedOrDeletedFormula(AddedOrDeletedFormula formula) {
                FormulaCell.this.pseudoClassStateChanged(PC_ADDED, formula.getType() == AddedOrDeletedFormula.Type.ADDED);
                FormulaCell.this.pseudoClassStateChanged(PC_DELETED, formula.getType() == AddedOrDeletedFormula.Type.DELETED);
                FormulaCell.this.pseudoClassStateChanged(PC_MODIFIED, false);
                return null;
            }

            @Override
            public Void visitModifiedFormula(ModifiedFormula formula) {
                FormulaCell.this.pseudoClassStateChanged(PC_ADDED, false);
                FormulaCell.this.pseudoClassStateChanged(PC_DELETED, false);
                FormulaCell.this.pseudoClassStateChanged(PC_MODIFIED, true);
                return null;
            }
        });
    }
}
