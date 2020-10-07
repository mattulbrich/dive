/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

public class ResolveUnicodeVisitor extends DafnyTreeDefaultVisitor<Void, Void> {

    @Override
    public Void visitUNICODE_INDEXED_ID(DafnyTree t, Void aVoid) {

        String chars = t.getText();
        int i = chars.length() - 1;
        StringBuilder sb = new StringBuilder();
        char c = chars.charAt(i);
        while(0x2080 <= c && c <= 0x2089 || c == '_') {
            if (c == '_') {
                sb.insert(0, c);
            } else {
                sb.insert(0, (char) (c - 0x2080 + '0'));
            }

            i--;
            c = chars.charAt(i);
        }

        sb.insert(0, chars.substring(0, i + 1) + '_');
        t.token.setType(DafnyParser.ID);
        t.token.setText(sb.toString());

        return aVoid;
    }
}
