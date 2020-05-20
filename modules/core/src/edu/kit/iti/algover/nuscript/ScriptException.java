/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ast.ScriptAST;
import edu.kit.iti.algover.proof.ProofNode;
import nonnull.NonNull;

public class ScriptException extends Exception {

    private final ScriptAST scriptAST;
    private final ProofNode proofNode;

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

    public ScriptAST getScriptAST() {
        return scriptAST;
    }

    public ProofNode getProofNode() {
        return proofNode;
    }
}
