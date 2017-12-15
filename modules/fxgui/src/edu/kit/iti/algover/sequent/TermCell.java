package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.css.PseudoClass;
import javafx.scene.control.ListCell;

import java.util.List;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermCell extends ListCell<TopLevelFormula> {

    private static final PseudoClass PC_ADDED = PseudoClass.getPseudoClass("term-added");
    private static final PseudoClass PC_DELETED = PseudoClass.getPseudoClass("term-deleted");
    private static final PseudoClass PC_MODIFIED = PseudoClass.getPseudoClass("term-modified");

    private final TermSelector.SequentPolarity polarity;
    private final SubSelection<TermSelector> referenceSelection;
    private final SubSelection<TermSelector> lastClickedTerm;
    private final SubSelection<AnnotatedString.TermElement> highlightedTerm;

    public TermCell(TermSelector.SequentPolarity polarity,
                    SubSelection<TermSelector> referenceSelection,
                    SubSelection<TermSelector> lastClickedTerm,
                    SubSelection<AnnotatedString.TermElement> highlightedTerm) {
        getStyleClass().add("term-cell");
        this.polarity = polarity;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;
        this.highlightedTerm = highlightedTerm;
    }

    @Override
    protected void updateItem(TopLevelFormula formula, boolean empty) {
        super.updateItem(formula, empty);
        if (!empty && formula != null) {
            setPseudoClasses(formula);
            setGraphic(new TermView(
                    formula,
                    referenceSelection.subSelection(this::updateSelectedSubterm, this::subtermToTermSelector),
                    lastClickedTerm.subSelection(this::updateSelectedSubterm, this::subtermToTermSelector),
                    highlightedTerm));
        } else {
            setPseudoClasses(null);
            setGraphic(null);
        }
    }

    protected void setPseudoClasses(TopLevelFormula formula) {
        if (formula != null) {
            setPseudoClassesFromChangeType(formula.getChangeType());
        } else {
            setPseudoClassesFromChangeType(TopLevelFormula.ChangeType.ORIGINAL);
        }
    }

    protected void setPseudoClassesFromChangeType(TopLevelFormula.ChangeType changeType) {
        System.out.println(getStyleClass());
        switch (changeType) {
            case ADDED:
                pseudoClassStateChanged(PC_ADDED, true);
                pseudoClassStateChanged(PC_DELETED, false);
                pseudoClassStateChanged(PC_MODIFIED, false);
                break;
            case DELETED:
                pseudoClassStateChanged(PC_ADDED, false);
                pseudoClassStateChanged(PC_DELETED, true);
                pseudoClassStateChanged(PC_MODIFIED, false);
                break;
            case MODIFIED:
                pseudoClassStateChanged(PC_ADDED, false);
                pseudoClassStateChanged(PC_DELETED, false);
                pseudoClassStateChanged(PC_MODIFIED, true);
                break;
            case ORIGINAL:
                pseudoClassStateChanged(PC_ADDED, false);
                pseudoClassStateChanged(PC_DELETED, false);
                pseudoClassStateChanged(PC_MODIFIED, false);
                break;
        }
        System.out.println(changeType);
        System.out.println(getPseudoClassStates());
    }

    private SubtermSelector updateSelectedSubterm(TermSelector termSelector) {
        if (termSelector != null && termSelector.getPolarity() == polarity && termSelector.getTermNo() == getIndex()) {
            return termSelector.getSubtermSelector();
        } else {
            return null;
        }
    }

    private TermSelector subtermToTermSelector(SubtermSelector subtermSelector) {
        List<Integer> pathAsList = subtermSelector.getPath();
        int[] path = new int[pathAsList.size()];
        for (int i = 0; i < path.length; i++) {
            path[i] = pathAsList.get(i);
        }
        return new TermSelector(polarity, getIndex(), path);
    }
}
