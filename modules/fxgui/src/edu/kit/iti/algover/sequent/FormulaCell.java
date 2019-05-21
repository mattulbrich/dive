package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.formulas.*;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.beans.Observable;
import javafx.collections.ObservableSet;
import javafx.collections.SetChangeListener;
import javafx.css.PseudoClass;
import javafx.scene.control.ListCell;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

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

    public void setSelectorsToHighlight(Set<TermSelector> selectorsToHighlight) {
        this.highlightSet = selectorsToHighlight;
    }

    private Set<TermSelector> highlightSet = new HashSet<>();

    public FormulaCell(TermSelector.SequentPolarity polarity,
                       SubSelection<TermSelector> referenceSelection,
                       SubSelection<TermSelector> lastClickedTerm,
                       SubSelection<AnnotatedString.TermElement> mouseOverTerm,
                       ObservableSet<TermSelector> selectorsToHighlight) {
        getStyleClass().add("formula-cell");
        this.polarity = polarity;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;
        this.mouseOverTerm = mouseOverTerm;
        selectorsToHighlight.addListener((SetChangeListener<TermSelector>) change -> {
     //       System.out.println("change = " + change);
            if (change.wasAdded()) {
                TermSelector elementAdded = change.getElementAdded();
                highlightSet.add(elementAdded);
            }
        });


    }


    @Override
    protected void updateItem(TopLevelFormula formula, boolean empty) {
        super.updateItem(formula, empty);
        //System.out.println("FormulaCell.updateItem");
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
                Set<TermSelector> filterAccToIndexInSeq = highlightSet.stream().filter(termSelector -> termSelector.getToplevelSelector().getTermNo() == formula.getIndexInSequent()).collect(Collectors.toSet());
                return new OriginalFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm, filterAccToIndexInSeq);
             //   return new OriginalFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm, new HashSet<>());
            }

            @Override
            public BasicFormulaView visitDeletedFormula(DeletedFormula formula) {
                return new BasicFormulaView(formula, mouseOverTerm, highlightSet);
            }

            @Override
            public BasicFormulaView visitAddedFormula(AddedFormula formula) {
                return new OriginalFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm, highlightSet);
            }

            @Override
            public BasicFormulaView visitModifiedFormula(ModifiedFormula formula) {
                return new ModifiedFormulaView(formula, polarity, referenceSelection, lastClickedTerm, mouseOverTerm, highlightSet);
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
