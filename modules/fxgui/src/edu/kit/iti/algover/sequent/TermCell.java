package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.util.BindingsUtil;
import javafx.beans.property.ObjectProperty;
import javafx.scene.control.ListCell;

import java.util.List;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermCell extends ListCell<Term> implements TermViewListener {

    private final SequentActionListener listener;
    private final TermSelector.SequentPolarity polarity;
    private final ObjectProperty<TermSelector> selectedTerm;

    public TermCell(TermSelector.SequentPolarity polarity, SequentActionListener listener, ObjectProperty<TermSelector> selectedTerm) {
        this.polarity = polarity;
        this.listener = listener;
        this.selectedTerm = selectedTerm;
    }

    @Override
    protected void updateItem(Term term, boolean empty) {
        super.updateItem(term, empty);
        if (!empty && term != null) {
            setGraphic(new TermView(term, this, BindingsUtil.convert(this::updateSelectedSubterm, selectedTerm)));
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

    @Override
    public void handleClickOnSubterm(boolean controlDown, Term term, SubtermSelector subtermSelector) {
        if (controlDown) {
            listener.requestReferenceHighlighting(subtermToTermSelector(subtermSelector));
        } else {
            listener.considerApplication(subtermToTermSelector(subtermSelector));
        }
    }

    @Override
    public void handleClickOutsideTerm() {
        getListView().getSelectionModel().select(getIndex());
        getListView().requestFocus();
        listener.requestReferenceHighlighting(null);
    }

    @Override
    public void handleSubtermSelection(AnnotatedString.TermElement highlightedElement) {
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
