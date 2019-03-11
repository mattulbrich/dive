package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.css.PseudoClass;
import javafx.scene.control.ListCell;

import java.util.HashSet;
import java.util.Set;

/**
 * Cell in ListView containing formulas
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
    private final Set<TermSelector> selectorsToHighlight;
    //TODO TermSelector auch anzeigen

    public FormulaCell(TermSelector.SequentPolarity polarity,
                       SubSelection<TermSelector> referenceSelection,
                       SubSelection<TermSelector> lastClickedTerm,
                       SubSelection<AnnotatedString.TermElement> mouseOverTerm) {
        getStyleClass().add("formula-cell");
        this.polarity = polarity;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;
        this.mouseOverTerm = mouseOverTerm;
        this.selectorsToHighlight = new HashSet<>();

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
            public BasicFormulaView visitDeletedFormula(DeletedFormula formula) {
                return new BasicFormulaView(formula, mouseOverTerm);
            }

            @Override
            public BasicFormulaView visitAddedFormula(AddedFormula formula) {
                return new OriginalFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm);
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
            public Void visitAddedFormula(AddedFormula formula) {
                FormulaCell.this.pseudoClassStateChanged(PC_ADDED, true);
                FormulaCell.this.pseudoClassStateChanged(PC_DELETED, false);
                FormulaCell.this.pseudoClassStateChanged(PC_MODIFIED, false);
                return null;
            }

            @Override
            public Void visitDeletedFormula(DeletedFormula formula) {
                FormulaCell.this.pseudoClassStateChanged(PC_ADDED, false);
                FormulaCell.this.pseudoClassStateChanged(PC_DELETED, true);
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
