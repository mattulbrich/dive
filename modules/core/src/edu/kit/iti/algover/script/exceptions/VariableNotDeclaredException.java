package edu.kit.iti.algover.script.exceptions;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class VariableNotDeclaredException extends InterpreterRuntimeException {
    public VariableNotDeclaredException() {
        super();
    }

    public VariableNotDeclaredException(String message) {
        super(message);
    }

    public VariableNotDeclaredException(String message, Throwable cause) {
        super(message, cause);
    }

    public VariableNotDeclaredException(Throwable cause) {
        super(cause);
    }

    protected VariableNotDeclaredException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
