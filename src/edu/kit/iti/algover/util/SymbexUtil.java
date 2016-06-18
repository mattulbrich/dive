/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;

public class SymbexUtil {

    public static String toString(SymbexPath res) {
        StringBuilder sb = new StringBuilder();
        sb.append("------------\n");
        sb.append(res.getPathIdentifier());
        sb.append("\n------------\n");

        for (PathConditionElement pc : res.getPathConditions()) {
            sb.append("Path condition - " + pc.getType() + "\n");
            sb.append("    " + pc.getExpression().toStringTree() + "\n");
            sb.append("  Assignment History:" + "\n");
            sb.append("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    ") + "\n");
            sb.append("  Refers to: line " + pc.getExpression().token.getLine() + "\n");
        }

        sb.append("Proof Obligations:\n");
        sb.append("  Assignment History:\n");
        sb.append("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
        for (AssertionElement po : res.getProofObligations()) {
            sb.append("  " + po + "\n");
        }

        return sb.toString();
    }

}
