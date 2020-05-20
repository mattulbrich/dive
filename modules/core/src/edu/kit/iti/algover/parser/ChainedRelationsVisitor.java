/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.Util;

import java.util.Arrays;
import java.util.BitSet;

import static edu.kit.iti.algover.parser.DafnyParser.*;
import static edu.kit.iti.algover.parser.DafnyParser.EQ;

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
public class ChainedRelationsVisitor
        extends DafnyTreeDefaultVisitor<Object, Void> {

    private static final BitSet CHAINABLE_TYPES =
            Util.bitSet(LE, LT, GE, GT, EQ);

    @Override
    public Object visitDefault(DafnyTree t, Void arg) {

        if (!CHAINABLE_TYPES.get(t.getType())) {
            return null;
        }

        // This is the unchained case
        if (t.getChildCount() == 2) {
            return null;
        }

        assert t.getChildCount() %2 == 0 :
                "Chained operators must have even number of subtrees";

        return act(t);
    }

    private Object act(DafnyTree t) {
        int direction = getRelDirection(t);

        // Original comparison
        DafnyTree last = t.getChild(1);
        DafnyTree result = new DafnyTree(t.getToken());
        result.addChild(t.getChild(0));
        result.addChild(t.getChild(1));

        // iterate over the chained cases
        for(int i = 2; i < t.getChildCount(); i += 2) {
            DafnyTree op = t.getChild(i);

            // check that direction is consistent
            int newdir = getRelDirection(op);
            if(direction * newdir < 0) {
                return new DafnyException("Illegally chained relational expressions", t);
            }
            direction += newdir;

            // create current comparison
            DafnyTree x = t.getChild(i + 1);
            DafnyTree comp = new DafnyTree(op.getToken());
            comp.addChild(last);
            comp.addChild(x);
            last = x;

            // rearrange into result
            DafnyTree newresult = new DafnyTree(DafnyParser.AND, "&&");
            newresult.addChild(result);
            newresult.addChild(comp);
            result = newresult;
        }

        int index = t.getChildIndex();
        t.getParent().replaceChildren(index, index, result);

        return result;
    }

    private static int getRelDirection(DafnyTree t) {
        switch(t.getType()) {
        case LT:
        case LE:
            return +1;
        case GE:
        case GT:
            return -1;
        case EQ:
            return 0;
        default:
            throw new Error("Unexpected case!");
        }
    }
}
