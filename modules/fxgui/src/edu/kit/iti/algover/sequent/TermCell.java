package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.term.Term;
import javafx.scene.control.ListCell;

/**
 * Created by Philipp on 22.07.2017.
 */
public class TermCell extends ListCell<Term> {
    @Override
    protected void updateItem(Term term, boolean empty) {
        super.updateItem(term, empty);
        if (!empty && term != null) {
            setText(null);
            setGraphic(new TermView(term));
        }
    }
}
