/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.script;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

/**
 * An pointer to a caharacter position within the proof script area.
 *
 * Besides the line and column, an object contains the type of the this indicator
 * and the proof node to which the checkpoint belongs.
 *
 * Both line and column are 1-based.
 *
 * @author Mattias Ulbrich
 */
public class ProofNodeCheckpoint {

    public enum Type {
        /**
         * This checkpoint indicates the beginning of a call statement
         */
        CALL,

        /**
         * This checkpoint indicates a range in which more than one branch exists.
         */
        BRANCH,

        /**
         * This indicates a proof node that does not have a rule application yet.
         */
        OPEN,

        /**
         * This indicates that this proof branch is closed.
         */
        CLOSED,
    }

    ;

    /**
     * The proof node to which this checkpoint refers
     */
    private final ProofNode proofNode;

    /**
     * The line in the proof script. First line is 1.
     */
    private final int line;

    /**
     * The column in the proof script. First column is 1.
     */
    private final int col;

    /**
     * The type of this indicator.
     */
    private final @NonNull Type type;

    public ProofNodeCheckpoint(ProofNode proofNode, int line, int col, Type type) {
        assert line >= 1;
        assert col >= 1;
        this.proofNode = proofNode;
        this.line = line;
        this.col = col;
        this.type = type;
    }

    public ProofNode getProofNode() {
        return proofNode;
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return col;
    }

    public Type getType() {
        return type;
    }

    @Override
    public String toString() {
        return "ProofNodeCheckpoint{" +
                "line=" + line +
                ", col=" + col +
                ", type=" + type +
                '}';
    }

    /**
     * Extract the list of checkpoints from a proof.
     *
     * The checkpoints in the result are in ascending order.
     *
     * @param proof extract the proof tree from this proof.
     * @return a freshly created, modifiable list
     */
    public static @DeepNonNull  List<ProofNodeCheckpoint> extractCheckpoints(@NonNull Proof proof) {
        ProofNode root = proof.getProofRoot();
        List<ProofNodeCheckpoint> checkpoints = new ArrayList<>();
        if (root != null) {
            // checkpoints.add(new ProofNodeCheckpoint(root, 0, 0, Type.CALL));
            build(root, checkpoints);
        }
        return checkpoints;
    }

    private static void build(ProofNode node, List<ProofNodeCheckpoint> checkpoints) {


        List<ProofNode> children = node.getChildren();
        Command command = node.getCommand();

        if(children != null) {
            if (children.isEmpty()) {
                // closed branch
                checkpoints.add(ProofNodeCheckpoint.endOf(command, node, Type.CLOSED));
            } else {
                // splitting branch
                Command commandOnThis = children.get(0).getCommand();
                checkpoints.add(ProofNodeCheckpoint.beginOf(commandOnThis, node, Type.CALL));
                if (children.size() > 1) {
                    checkpoints.add(ProofNodeCheckpoint.endOf(commandOnThis, node, Type.BRANCH));
                }

                for (ProofNode child : children) {
                    build(child, checkpoints);
                }
            }
        } else {
            checkpoints.add(ProofNodeCheckpoint.endOf(command, node, Type.OPEN));
        }
    }

    private static ProofNodeCheckpoint endOf(Command cmd, ProofNode node, Type type) {
        Token token = cmd.getEndToken();
        return new ProofNodeCheckpoint(node, token.getLine(),
                token.getCharPositionInLine() + token.getText().length() + 1, type);
    }

    private static ProofNodeCheckpoint beginOf(Command cmd, ProofNode node, Type type) {
        Token token = cmd.getBeginToken();
        return new ProofNodeCheckpoint(node, token.getLine(),
                token.getCharPositionInLine() + 1, type);
    }
}
