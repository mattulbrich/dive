/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.exceptions;

/**
 * Exception that is thrown if State graph could not be build properly
 */
public class StateGraphException extends RuntimeException {
    public StateGraphException() {
        super();
    }

    public StateGraphException(String message) {
        super(message);
    }

    public StateGraphException(String message, Throwable cause) {
        super(message, cause);
    }

    public StateGraphException(Throwable cause) {
        super(cause);
    }

    protected StateGraphException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
