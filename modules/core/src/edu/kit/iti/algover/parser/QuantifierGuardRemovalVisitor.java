/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

public class QuantifierGuardRemovalVisitor {

    public void walk(DafnyTree tree) {
        switch(tree.getType()) {
        case DafnyParser.ALL:
        case DafnyParser.EX:
            int childCount = tree.getChildCount();
            DafnyTree penultimate = tree.getChild(childCount - 2);
            if (penultimate.getType() == DafnyParser.CARD) {
                int connType = tree.getType() == DafnyParser.ALL ? DafnyParser.IMPLIES : DafnyParser.AND;
                DafnyTree connect = new DafnyTree(connType);
                connect.addChild(penultimate.getChild(0));
                connect.addChild(tree.getLastChild());
                tree.setChild(childCount - 2, connect);
                tree.replaceChildren(childCount - 2, childCount - 1, connect);
            }
        default:
            tree.getChildren().forEach(this::walk);
        }
    }
}
