/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

public class ChainedRelationsVisitor {

    public void walk(DafnyTree t) throws DafnyException {

        int relType = getRelType(t);
        if(relType != 0) {
            DafnyTree left = t.getChild(0);
            int leftRelType = getRelType(left);
            if(leftRelType == relType) {
                walk(act(t));
                return;
            } else if(leftRelType != 0) {
                throw new DafnyException("Illegally chained relational expression", t);
            }
        }

        for (DafnyTree child : t.getChildren()) {
            walk(child);
        }
    }

    /*
     * Identified is (a <= b) <= c or similar. left is (a <= b)
     * Make that into (a <= b) && (b <= c)
     */
    private DafnyTree act(DafnyTree t) {
        int index = t.getChildIndex();
        DafnyTree left = t.getChild(0);
        DafnyTree a = left.getChild(0);
        DafnyTree b = t.getChild(0).getChild(1);
        DafnyTree c = t.getChild(1);

        DafnyTree replacement = new DafnyTree(DafnyParser.AND, "&&");
        t.getParent().replaceChildren(index, index, replacement);

        t.removeAllChildren();
        t.addChild(b);
        t.addChild(c);

        replacement.addChild(left);
        replacement.addChild(t);


        return replacement;
    }

    private static int getRelType(DafnyTree t) {
        switch(t.getType()) {
        case DafnyParser.LT:
        case DafnyParser.LE:
            return -1;
        case DafnyParser.GE:
        case DafnyParser.GT:
            return 1;
        default:
            return 0;
        }
    }
}
