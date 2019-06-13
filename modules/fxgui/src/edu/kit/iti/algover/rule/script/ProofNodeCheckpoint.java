/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;

/**
 * An object representing one Position in the script at which a command ends such that a new
 * ProofNode should be shown when passen this point with the cursor.
 */
public class ProofNodeCheckpoint {

    /**
     * The position at which the another ProofNode is shown.
     */
    public final Position position;
    /**
     * The ASTNode which represents the completed command (this used to find the corresponding ProofNode).
     */
    public final ASTNode node;

    public ProofNodeCheckpoint(Position pos, ASTNode node) {
        position = pos;
        this.node = node;
    }

    @Override
    public String toString() {
        return "ProofNodeCheckpoint{" +
                "position=" + position +
                ", node =" + node +
                '}';
    }
}
