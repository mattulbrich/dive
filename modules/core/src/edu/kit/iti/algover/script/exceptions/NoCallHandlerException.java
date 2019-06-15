/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.exceptions;


import edu.kit.iti.algover.script.ast.CallStatement;

/**
 * @author Alexander Weigl
 * @version 1 (29.05.17)
 */
public class NoCallHandlerException extends InterpreterRuntimeException {
    public CallStatement callStatement;

    public NoCallHandlerException() {
        super();
    }

    public NoCallHandlerException(String message) {
        super(message);
    }

    public NoCallHandlerException(String message, Throwable cause) {
        super(message, cause);
    }

    public NoCallHandlerException(Throwable cause) {
        super(cause);
    }

    protected NoCallHandlerException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public NoCallHandlerException(CallStatement callStatement) {
        super(callStatement.toString());
        this.callStatement = callStatement;
    }
}
