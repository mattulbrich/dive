/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.script;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;
import nonnull.DeepNonNull;
import nonnull.NonNull;

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

    enum Type {
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
        OPEN };

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
            build(root, checkpoints);
        }
        return checkpoints;
    }

    private static void build(ProofNode node, List<ProofNodeCheckpoint> checkpoints) {

        Position pos = node.getBeginPos();
        List<ProofNode> children = node.getChildren();
        ASTNode mutator = null;
        if (!node.getMutator().isEmpty()) {
            mutator = node.getMutator().get(0);
        }

        if (mutator != null) {
            checkpoints.add(new ProofNodeCheckpoint(node, pos.getLineNumber(), pos.getCharInLine() + 1, Type.CALL));
            if (children.size() > 1) {
                ASTNode ast = node.getMutator().get(0);
                Position end = ast.getEndPosition();
                checkpoints.add(new ProofNodeCheckpoint(node, end.getLineNumber(), end.getCharInLine()+2, Type.BRANCH));
            }
        } else {
            if (pos != null) {
                checkpoints.add(new ProofNodeCheckpoint(node, pos.getLineNumber(), pos.getCharInLine() + 2, Type.OPEN));
            }
        }

/*
        if(pos != null) {
            Type type = node.getMutator().isEmpty() ? Type.OPEN : Type.CALL;
            checkpoints.add(new ProofNodeCheckpoint(node, pos.getLineNumber(), pos.getCharInLine() + 1, type));
        }

        if (children.isEmpty()) {
            if (!node.isClosed() && !node.getMutator().isEmpty()) {
                ASTNode ast = node.getMutator().get(0);
                Position end = ast.getEndPosition();
                checkpoints.add(new ProofNodeCheckpoint(node, end.getLineNumber(), end.getCharInLine()+2, Type.OPEN));
            }
        } else

        if (children.size() > 1) {
            ASTNode ast = node.getMutator().get(0);
            Position end = ast.getEndPosition();
            checkpoints.add(new ProofNodeCheckpoint(node, end.getLineNumber(), end.getCharInLine()+2, Type.BRANCH));
        }
*/
        for (ProofNode child : children) {
            build(child, checkpoints);
        }

    }
}
