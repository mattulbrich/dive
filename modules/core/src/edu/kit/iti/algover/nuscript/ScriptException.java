/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.proof.ProofNode;
import nonnull.NonNull;

/**
 * Exception thrown during interpretation of a script.
 *
 * Instances have a pointer to an instance of the script ast.
 *
 * @author Mattias Ulbrich
 */
public class ScriptException extends Exception {

    private final @NonNull ScriptAST scriptAST;
    private final @NonNull ProofNode proofNode;

    public ScriptException(String message, @NonNull ScriptAST ast, @NonNull ProofNode proofNode) {
        super(message);
        this.scriptAST = ast;
        this.proofNode = proofNode;
    }

    public ScriptException(Throwable cause, @NonNull ScriptAST ast, @NonNull ProofNode proofNode) {
        super(cause);
        this.scriptAST = ast;
        this.proofNode = proofNode;
    }

    public ScriptException(String message, Throwable cause, ScriptAST ast, @NonNull ProofNode proofNode) {
        super(message, cause);
        this.scriptAST = ast;
        this.proofNode = proofNode;
    }

    public @NonNull ScriptAST getScriptAST() {
        return scriptAST;
    }

    public @NonNull ProofNode getProofNode() {
        return proofNode;
    }
}
