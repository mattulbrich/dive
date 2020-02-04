/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ast.ScriptAST;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Parameter;
import edu.kit.iti.algover.rules.RuleException;
import nonnull.NonNull;

public class ScriptException extends Exception {

    private final ScriptAST scriptAST;

    public ScriptException(String message, @NonNull ScriptAST ast) {
        super(message);
        this.scriptAST = ast;
    }

    public ScriptException(Throwable cause, @NonNull ScriptAST ast) {
        super(cause);
        this.scriptAST = ast;
    }

    public ScriptException(String message, Throwable cause, ScriptAST ast) {
        super(message, cause);
        this.scriptAST = ast;
    }

    public ScriptAST getScriptAST() {
        return scriptAST;
    }
}
