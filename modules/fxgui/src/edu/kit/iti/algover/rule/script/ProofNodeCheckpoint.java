/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.Position;
import edu.kit.iti.algover.proof.ProofNodeSelector;

public class ProofNodeCheckpoint {

    public final ProofNodeSelector selector;
    public final Position position;
    public final Position caretPosition;

    public ProofNodeCheckpoint(ProofNodeSelector selector, Position position, Position caretPosition) {
        this.selector = selector;
        this.position = position;
        // caret position is real line number and not indexed line number
        this.caretPosition = caretPosition;
    }

    @Override
    public String toString() {
        return "ProofNodeCheckpoint{" +
                "selector=" + selector +
                ", position=" + position +
                ", caretPosition=" + caretPosition +
                '}';
    }
}
