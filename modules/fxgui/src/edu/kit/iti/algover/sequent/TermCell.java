package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import javafx.scene.control.ListCell;

import java.util.List;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermCell extends ListCell<Term> implements TermViewListener {

    private final SequentActionListener listener;
    private final TermSelector.SequentPolarity polarity;

    public TermCell(TermSelector.SequentPolarity polarity, SequentActionListener listener) {
        this.polarity = polarity;
        this.listener = listener;
    }

    @Override
    protected void updateItem(Term term, boolean empty) {
        super.updateItem(term, empty);
        if (!empty && term != null) {
            setGraphic(new TermView(term, this));
        } else {
            setGraphic(null);
        }
    }

    @Override
    public void handleClickOnSubterm(Term term, SubtermSelector subtermSelector) {
        List<Integer> pathAsList = subtermSelector.getPath();
        int[] path = new int[pathAsList.size()];
        for (int i = 0; i < path.length; i++) {
            path[i] = pathAsList.get(i);
        }
        listener.clickOnSubterm(new TermSelector(polarity, getIndex(), path));
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
