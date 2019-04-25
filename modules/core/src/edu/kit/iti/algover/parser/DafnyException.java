/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;


import java.io.File;

/**
 * The Class DafnyException is thrown by all routines that have a
 * {@link DafnyTree} at hand.
 *
 * @author Mattias Ulbrich
 */
@SuppressWarnings("serial")
public class DafnyException extends Exception {

    /**
     * The tree to which this exception relates.
     */
    private final DafnyTree tree;

    // Checkstyle: OFF JavadocMethodCheck

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
        super(cause.getMessage(), cause);
        this.tree = tree;
    }

    public DafnyTree getTree() {
        return tree;
    }

    @Override
    public String getMessage() {
        String result = "";
        if (tree != null) {
            if (tree.getFilename() == null) {
                return super.getMessage();
            }
            result += new File(tree.getFilename()).getName() + ":" + tree.getLine()
                    + ":" + tree.getCharPositionInLine() + super.getMessage();
        }
        return result;
    }

}
