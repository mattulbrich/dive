/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.util.Pair;

/**
 * Created by sarah on 8/30/16.
 */
public class Assignment {
    private int lineNumber;

    public String getRightSide() {
        return rightSide;
    }

    public String getLeftSide() {
        return leftSide;
    }

    public Pair<String, DafnyTree> getOriginalRepresentation() {
        return originalRepresentation;
    }

    public int getLineNumber() {
        return lineNumber;
    }

    private String rightSide;
    private String leftSide;

    private Pair<String, DafnyTree> originalRepresentation;

    public Assignment(Pair<String, DafnyTree> representation){
        this.originalRepresentation = representation;
        this.rightSide = representation.getSnd().toStringTree();
        this.leftSide = representation.getFst();
        this.lineNumber = representation.getSnd().token.getLine();
    }
}
