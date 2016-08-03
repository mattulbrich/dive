/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;


/**
 * The Class DafnyException is thrown by all routines that have a
 * {@link DafnyTree} at hand.
 *
 * @author Mattias Ulbrich
 */
@SuppressWarnings("serial")
public class DafnyException extends Exception {

    private final DafnyTree tree;

    public DafnyException(DafnyTree tree) {
        super();
        this.tree = tree;
    }

    public DafnyException(String message, DafnyTree tree, Throwable cause) {
        super(message, cause);
        this.tree = tree;
    }

    public DafnyException(String message, DafnyTree tree) {
        super(message);
        this.tree = tree;
    }

    public DafnyException(DafnyTree tree, Throwable cause) {
        super(cause);
        this.tree = tree;
    }

    public DafnyTree getTree() {
        return tree;
    }

}
