/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.exceptions;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class VariableNotDefinedException extends InterpreterRuntimeException {
    public VariableNotDefinedException() {
        super();
    }

    public VariableNotDefinedException(String message) {
        super(message);
    }

    public VariableNotDefinedException(String message, Throwable cause) {
        super(message, cause);
    }

    public VariableNotDefinedException(Throwable cause) {
        super(cause);
    }

    protected VariableNotDefinedException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
