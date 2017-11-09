package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.SubSelection;
import javafx.beans.Observable;
import javafx.beans.value.ObservableValue;
import javafx.scene.control.ListCell;

import java.util.List;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermCell extends ListCell<Term> {

    private final TermSelector.SequentPolarity polarity;
    private final SubSelection<TermSelector> referenceSelection;
    private final SubSelection<TermSelector> lastClickedTerm;
    private final SubSelection<AnnotatedString.TermElement> highlightedTerm;

    public TermCell(TermSelector.SequentPolarity polarity,
                    SubSelection<TermSelector> referenceSelection,
                    SubSelection<TermSelector> lastClickedTerm,
                    SubSelection<AnnotatedString.TermElement> highlightedTerm) {
        this.polarity = polarity;
        this.referenceSelection = referenceSelection;
        this.lastClickedTerm = lastClickedTerm;
        this.highlightedTerm = highlightedTerm;
        highlightedTerm.selected().addListener(invalidation -> resetListSelectionOnInnerTermSelection());
        lastClickedTerm.selected().addListener(this::handleTopLevelTermSelect);
    }

    @Override
    protected void updateItem(Term term, boolean empty) {
        super.updateItem(term, empty);
        if (!empty && term != null) {
            setGraphic(new TermView(
                    term,
                    referenceSelection.subSelection(this::updateSelectedSubterm, this::subtermToTermSelector),
                    lastClickedTerm.subSelection(this::updateSelectedSubterm, this::subtermToTermSelector),
                    highlightedTerm));
        } else {
            setGraphic(null);
        }
    }

    private SubtermSelector updateSelectedSubterm(TermSelector termSelector) {
        if (termSelector != null && termSelector.getPolarity() == polarity && termSelector.getTermNo() == getIndex()) {
            return termSelector.getSubtermSelector();
        } else {
            return null;
        }
    }

    private void handleTopLevelTermSelect(ObservableValue<? extends TermSelector> observable, TermSelector before, TermSelector selector) {
        getListView().getSelectionModel().select(getIndex());
        getListView().requestFocus();
        highlightedTerm.unsetGobally();
    }

    private void resetListSelectionOnInnerTermSelection() {
        getListView().getSelectionModel().clearSelection();
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
