/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;

// TODO Move to tests?
public class SymbexUtil {

    private SymbexUtil() {
        throw new Error();
    }

    /**
     * Turn a symb. execution path into a readable string.
     * Mainly for debugging purposes.
     *
     * @param res the path to display
     * @return a multi-line string description
     */
    public static String toString(SymbexPath res) {
        StringBuilder sb = new StringBuilder();
        sb.append("------------\n");
        sb.append(res.getPathIdentifier());
        sb.append("\n------------\n");

        for (PathConditionElement pc : res.getPathConditions()) {
            sb.append("Path condition - " + pc.getType() + "\n");
            sb.append("    " + pc.getExpression().toStringTree() + "\n");
            sb.append("  Assignment History:" + "\n");
            sb.append("    "
                    + Util.join(pc.getAssignmentHistory().map(DafnyTree::toStringTree), "\n    ")
                    + "\n");
            sb.append("  Refers to: line " + pc.getExpression().token.getLine() + "\n");
        }

        sb.append("Proof Obligations:\n");
        sb.append("  Assignment History:\n");
        sb.append("    " + Util.join(res.getAssignmentHistory().map(DafnyTree::toStringTree),
                                "\n    "));
        sb.append("\n");
        for (AssertionElement po : res.getProofObligations()) {
            sb.append("  " + po + "\n");
        }

        return sb.toString();
    }

}
