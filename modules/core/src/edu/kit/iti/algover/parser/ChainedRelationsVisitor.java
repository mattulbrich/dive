/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import static edu.kit.iti.algover.parser.ChainedRelationsVisitor.Direction.*;

/**
 * This syntactic sugar resolution routine resolves chained integer comparison.
 *
 * {@code a < b < c} becomes {@code a < b && b < c}.
 *
 * Equality can also be chained in Dafny.
 *
 * Direction must not be inverted within the chain.
 *
 * @see SyntacticSugarVistor
 * @author mulbrich
 */
public class ChainedRelationsVisitor {

    enum Direction { ASC, DESC, EQ, leftRelType, NO_COMP };

    public void walk(DafnyTree t) throws DafnyException {

        Direction relDir = getRelDirection(t);
        if(relDir != NO_COMP) {
            DafnyTree left = t.getChild(0);
            Direction leftRelDir = getRelDirection(left);
            if(isCompatible(relDir, leftRelDir)) {
                walk(act(t));
                return;
            } else if(leftRelDir != NO_COMP) {
                throw new DafnyException("Illegally chained relational expressions", t);
            }
        }

        for (DafnyTree child : t.getChildren()) {
            walk(child);
        }
    }

    private static boolean isCompatible(Direction d1, Direction d2) {
        return d1 != NO_COMP && d2 != NO_COMP &&
                (d1 == d2 || d1 == EQ || d2 == EQ);
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
        t.addChild(b.dupTree());
        t.addChild(c);

        replacement.addChild(left);
        replacement.addChild(t);

        return replacement;
    }

    private static Direction getRelDirection(DafnyTree t) {
        switch(t.getType()) {
        case DafnyParser.LT:
        case DafnyParser.LE:
            return ASC;
        case DafnyParser.GE:
        case DafnyParser.GT:
            return DESC;
        case DafnyParser.EQ:
            return EQ;
        default:
            return NO_COMP;
        }
    }
}
