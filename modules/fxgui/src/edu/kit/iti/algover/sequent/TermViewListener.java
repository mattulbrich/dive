package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;

/**
 * Created by philipp on 02.08.17.
 */
public interface TermViewListener {
    void handleClickOnSubterm(boolean controlDown, Term term, SubtermSelector subtermSelector);

    void handleClickOutsideTerm();

    void handleSubtermSelection(AnnotatedString.TermElement highlightedElement);
}
