/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import org.antlr.v4.runtime.Token;

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

    /**
     * The proof node to which this checkpoint refers
     */
    private final ProofNode proofNode;

    private final ScriptAST ast;

    private final boolean afterStmt;

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

    public ProofNodeCheckpoint(ProofNode proofNode, ScriptAST ast, boolean afterStmt,
                               int line, int col, Type type) {
        assert line >= 1;
        assert col >= 1;
        this.ast = ast;
        this.afterStmt = afterStmt;
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

    public ScriptAST getAst() {
        return ast;
    }

    public boolean isAfterStmt() {
        return afterStmt;
    }

    @Override
    public String toString() {
        String ret = "ProofNodeCheckpoint{" +
                "AST (Statement)=" + this.ast +
                ", end?= " + this.afterStmt;

        if (proofNode == null) {
            ret += ", ProofNode= null";
        } else {
            ret += (", ProofNode= " + new ProofNodeSelector(proofNode));
        }

        ret += ", line=" + line +
                ", col=" + col +
                ", type=" + type +
                '}';
        return ret;
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

        ProofNodeCheckpointBuilder builder = new ProofNodeCheckpointBuilder(proof);

        if (builder.canCollect()) {
            builder.collectCheckpoints();
            return builder.getCheckpoints();
        } else {
            return List.of();
        }
    }

    static ProofNodeCheckpoint endOf(ScriptAST parent, ScriptAST cmd, ProofNode node, Type type) {
        Token token = cmd.getEndToken();
        return new ProofNodeCheckpoint(node, parent, true, token.getLine(),
                token.getCharPositionInLine() + token.getText().length() + 1, type);
    }

    static ProofNodeCheckpoint beginOf(ScriptAST parent, ScriptAST cmd, ProofNode node, Type type) {
        Token token = cmd.getBeginToken();
        return new ProofNodeCheckpoint(node, parent, false, token.getLine(),
                token.getCharPositionInLine() + 1, type);
    }
}
