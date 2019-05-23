/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.interpreter;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.Signature;
import edu.kit.iti.algover.script.data.VariableAssignment;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.17)
 */
public interface MatcherApi<T> {
    List<VariableAssignment> matchLabel(ProofNode currentState, String label);

    List<VariableAssignment> matchSeq(ProofNode currentState, String data, Signature sig);

}
