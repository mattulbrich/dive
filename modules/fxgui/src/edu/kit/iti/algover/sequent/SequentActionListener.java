package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;

/**
 * Created by Philipp on 13.08.2017.
 */
public interface SequentActionListener {

    void cancelProofEditing();

    void clickOnSubterm(TermSelector selector);

}
