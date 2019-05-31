/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.script;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.Position;

public class ProofNodeCheckpoint {

    public final ProofNodeSelector selector;
    public final Position position;
    public final Position caretPosition;

    public ProofNodeCheckpoint(ProofNodeSelector selector, Position position, Position caretPosition) {
        this.selector = selector;
        this.position = position;
        //caret position is real line number and not indexed line number
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