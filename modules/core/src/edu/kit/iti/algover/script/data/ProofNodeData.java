package edu.kit.iti.algover.script.data;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;

/**
 * Created by sarah on 8/17/17.
 */
public class ProofNodeData {

    ProofNode pn;
    Sequent seq;

    public ProofNodeData(ProofNode proofRoot) {
        pn = proofRoot;
        this.seq = proofRoot.getSequent();
    }
}
