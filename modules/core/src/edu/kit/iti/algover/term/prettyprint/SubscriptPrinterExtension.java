/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SubscriptPrinterExtension implements PrettyPrintExtension {

    private static final String SUBSCRIPT_PATTERN = "(.*)_([0-9]+)";
    private static final int SUBSCRIPT_BASE = 0x2080;

    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        return functionSymbol.getArity() == 0
                && functionSymbol.getName().matches(SUBSCRIPT_PATTERN);
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        return Integer.MAX_VALUE;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        return Integer.MAX_VALUE;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        String name = application.getFunctionSymbol().getName();
        Matcher matcher = Pattern.compile(SUBSCRIPT_PATTERN).matcher(name);
        if (matcher.matches()) {
            StringBuilder sb = new StringBuilder(matcher.group(1));
            String index = matcher.group(2);
            for (int i = 0; i < index.length(); i++) {
                 sb.append((char)(SUBSCRIPT_BASE + index.charAt(i) - '0'));
            }
            visitor.getPrinter().append(sb.toString());
        } else {
            // This should never happen!
            // TODO Add logging
            visitor.getPrinter().append(name);
        }
    }
}
