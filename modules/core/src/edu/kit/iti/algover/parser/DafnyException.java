/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;


import nonnull.NonNull;

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

    public DafnyException(@NonNull DafnyTree tree) {
        super();
        this.tree = tree;
    }

    public DafnyException(String message, @NonNull DafnyTree tree, Throwable cause) {
        super(message, cause);
        this.tree = tree;
    }

    public DafnyException(String message, @NonNull DafnyTree tree) {
        super(message);
        this.tree = tree;
    }

    public DafnyException(@NonNull DafnyTree tree, Throwable cause) {
        super(cause.getMessage(), cause);
        this.tree = tree;
    }

    public DafnyTree getTree() {
        return tree;
    }

    /*@Override
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
    }*/

}
