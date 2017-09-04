package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import javafx.scene.control.ListCell;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermCell extends ListCell<Term> implements TermViewListener {
    @Override
    protected void updateItem(Term term, boolean empty) {
        super.updateItem(term, empty);
        if (!empty && term != null) {
            setText(null);
            setGraphic(new TermView(term, this));
        }
    }

    @Override
    public void handleClickOnSubterm(Term term, SubtermSelector subtermSelector) {
        // TODO: Implement another view animation to the right
        // for selecting the rules for applying to the term or
        // seeing the history of a term
    }

    @Override
    public void handleClickOutsideTerm() {
        getListView().getSelectionModel().select(getIndex());
        getListView().requestFocus();
    }

    @Override
    public void handleSubtermSelection(AnnotatedString.TermElement highlightedElement) {
        getListView().getSelectionModel().clearSelection();
    }
}
