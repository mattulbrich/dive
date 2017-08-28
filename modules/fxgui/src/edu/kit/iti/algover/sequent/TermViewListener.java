package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;

/**
 * Created by philipp on 02.08.17.
 */
public interface TermViewListener {
    void handleClickOnSubterm(Term term, SubtermSelector subtermSelector);

    void handleClickOutsideTerm();

}
