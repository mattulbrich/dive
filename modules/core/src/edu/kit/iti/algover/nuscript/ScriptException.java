/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.proof.ProofNode;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * Exception thrown during interpretation of a script.
 *
 * Instances have a pointer to an instance of the script ast.
 *
 * @author Mattias Ulbrich
 */
public class ScriptException extends Exception {

    private final @NonNull ScriptAST scriptAST;
    private final @Nullable ProofNode proofNode;

    public ScriptException(String message, @NonNull ScriptAST ast, @Nullable ProofNode proofNode) {
        super(message);
        this.scriptAST = ast;
        this.proofNode = proofNode;
    }

    public ScriptException(Throwable cause, @NonNull ScriptAST ast, @Nullable ProofNode proofNode) {
        super(cause);
        this.scriptAST = ast;
        this.proofNode = proofNode;
    }

    public ScriptException(String message, Throwable cause, @NonNull ScriptAST ast, @Nullable ProofNode proofNode) {
        super(message, cause);
        this.scriptAST = ast;
        this.proofNode = proofNode;
    }

    public ScriptException(String message, ScriptAST ast) {
        this(message, ast, null);
    }

    public @NonNull ScriptAST getScriptAST() {
        return scriptAST;
    }

    public @Nullable ProofNode getProofNode() {
        return proofNode;
    }
}
