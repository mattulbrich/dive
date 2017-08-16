/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

/**
 * The Class RuleException can be used to indicate sth is wrong when operating
 * with proof rules.
 *
 * @author Mattias Ulbrich
 */
@SuppressWarnings("serial")
public class RuleException extends Exception {

    // Checkstyle: OFF JavadocMethod

    public RuleException() {
        super();
    }

    public RuleException(String message, Throwable cause, boolean enableSuppression,
                         boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public RuleException(String message, Throwable cause) {
        super(message, cause);
    }

    public RuleException(String message) {
        super(message);
    }

    public RuleException(Throwable cause) {
        super(cause);
    }

}
