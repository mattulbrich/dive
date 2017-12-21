package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.rules.TermSelector;

/**
 * Created by Philipp on 13.08.2017.
 */
public interface SequentActionListener {

    void onClickSequentSubterm(TermSelector selector);

    void onRequestReferenceHighlighting(ProofTermReference termReference);
}
