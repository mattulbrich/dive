/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.proof.PVCCollection;

public class Debug {


    public static CharSequence prettyPrint(CharSequence cs) {

        int len = cs.length();
        int level = 0;
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < len; i++) {

            char c = cs.charAt(i);
            switch(c) {
            case '(':
                level++;
                sb.append("\n").append(Util.duplicate(" ", level));
                break;
            case ')':
                level--;
                break;
            }
            sb.append(c);
        }

        return sb;

    }

    public static CharSequence toString(PVCCollection coll)  {
        StringBuilder sb = new StringBuilder();
        toString(sb, coll, 0);
        return sb;
    }

    private static void toString(StringBuilder sb, PVCCollection coll, int indent) {
        sb.append(Util.duplicate("   ", indent))
            .append(coll.toString())
            .append("\n");
        for (PVCCollection child : coll.getChildren()) {
            toString(sb, child, indent + 1);
        }
    }

}
