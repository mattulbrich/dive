/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

/**
 * This syntactic sugar resolution replaces guards in quantifiers by
 * implication or conjunction.
 *
 * {@code forall i:int | i > 1 :: i > 0} is replaced by
 * {@code forall i:int :: i > 1 ==> i > 0}.
 *
 * {@code exists i:int | i > 1 :: i > 0} is replaced by
 * {@code exists i:int :: i > 1 && i > 0}.
 *
 * @author mulbrich
 * @see SyntacticSugarVistor
 */
public class QuantifierGuardRemovalVisitor extends DafnyTreeDefaultVisitor<Void, Void> {

    @Override
    public Void visitEX(DafnyTree t, Void aVoid) {
        walk(t);
        return null;
    }

    @Override
    public Void visitALL(DafnyTree t, Void aVoid) {
        walk(t);
        return null;
    }

    public void walk(DafnyTree tree) {
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
    }
}
