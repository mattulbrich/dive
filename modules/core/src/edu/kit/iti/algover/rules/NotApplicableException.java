/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules;

public class NotApplicableException extends RuleException {
    public NotApplicableException() {
    }

    public NotApplicableException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public NotApplicableException(String message, Throwable cause) {
        super(message, cause);
    }

    public NotApplicableException(String message) {
        super(message);
    }

    public NotApplicableException(Throwable cause) {
        super(cause);
    }
}
