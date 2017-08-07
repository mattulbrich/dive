package edu.kit.iti.algover.script.exceptions;

import edu.kit.formal.proofscriptparser.ast.CallStatement;

/**
 * @author Alexander Weigl
 * @version 1 (29.05.17)
 */
public class NoCallHandlerException extends InterpreterRuntimeException {
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
    }
}
