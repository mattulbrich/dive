package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.rules.TermSelector;
import javafx.beans.Observable;

/**
 * Created by Philipp on 13.08.2017.
 */
public interface SequentActionListener {

    void onClickSequentSubterm(TermSelector selector);

    void onRequestReferenceHighlighting(ProofTermReferenceTarget termReference);

    void onSwitchViewedNode(ProofNodeSelector proofNodeSelector);

}
