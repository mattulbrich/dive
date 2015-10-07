package edu.kit.iti.algover.Proof;

import edu.kit.iti.algover.parser.DafnyTree;

import java.util.LinkedList;

/**
 * Created by sarah on 10/7/15.
 */
public class ProofInstance {

    private ProofNode root;
    private DafnyTree pvc;
    // I think the follwing might be unnecessary
    private LinkedList<ProofFormula> original_pvc_with_focus;
}
