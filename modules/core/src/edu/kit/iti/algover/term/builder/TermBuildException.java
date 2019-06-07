/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.parser.DafnyTree;

public class TermBuildException extends Exception {

    private DafnyTree location;

    public TermBuildException() {
        super();
    }

    public TermBuildException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public TermBuildException(String message, Throwable cause) {
        super(message, cause);
    }

    public TermBuildException(String message) {
        super(message);
    }

    public TermBuildException(Throwable cause) {
        super(cause);
    }

    public DafnyTree getLocation() {
        return location;
    }

    public TermBuildException setLocation(DafnyTree location) {
        this.location = location;
        return this;
    }

    public TermBuildException setLocationIfUnset(DafnyTree location) {
        if(!hasLocation()) {
            setLocation(location);
        }
        return this;
    }

    public boolean hasLocation() {
        return location != null;
    }
}
