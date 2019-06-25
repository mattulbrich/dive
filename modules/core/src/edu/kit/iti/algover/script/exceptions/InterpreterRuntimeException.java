/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.exceptions;

import edu.kit.iti.algover.script.ast.ASTNode;

/**
 * Exceptions that can occur during the runtime of the Interpreter reveiling internal problems of the interpreter
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class InterpreterRuntimeException extends RuntimeException {
    /**
     * ASTNode that is currently interpreted when the Exception is raised
     */
    private ASTNode location;

    /**
     * Get the ASTNode that is currently interpreted when the Exception is raised
     */
    public ASTNode getLocation() {
        return location;
    }

    public void setLocation(ASTNode location) {
        this.location = location;
    }

    public InterpreterRuntimeException() {
        super();
    }

    public InterpreterRuntimeException(String message) {
        super(message);
    }

    public InterpreterRuntimeException(String message, Throwable cause) {
        super(message, cause);
    }

    public InterpreterRuntimeException(Throwable cause) {
        super(cause);
    }

    protected InterpreterRuntimeException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

}
