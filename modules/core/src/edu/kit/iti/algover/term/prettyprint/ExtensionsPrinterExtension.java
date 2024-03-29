/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.Term;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ExtensionsPrinterExtension implements PrettyPrintExtension {
    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        return  isInstanceOf(functionSymbol, BuiltinSymbols.SET_ADD) ||
                isInstanceOf(functionSymbol, BuiltinSymbols.SEQ_CONS) ||
                isInstanceOf(functionSymbol, BuiltinSymbols.MULTI_SET_ADD);
    }

    private boolean isInstanceOf(FunctionSymbol functionSymbol, FunctionSymbolFamily family) {
        if (functionSymbol instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol isymb = (InstantiatedFunctionSymbol) functionSymbol;
            FunctionSymbolFamily foundFamily = isymb.getFamily();
            return foundFamily == family;
        }
        return false;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        // very high number since it starts with an unambigouous token ']'
        return 1000;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        // very high number since it ends with an unambigouous token ']'
        return 1000;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor prettyPrintVisitor) {
        FunctionSymbol firstFS = application.getFunctionSymbol();
        List<Term> collectedEntries = new ArrayList<>();

        Term t = application;
        FunctionSymbol fs = firstFS;
        while(fs == firstFS) {
            collectedEntries.add(t.getTerm(0));
            t = t.getTerm(1);
            if(t instanceof ApplTerm) {
                ApplTerm a = (ApplTerm) t;
                fs = a.getFunctionSymbol();
            } else {
                fs = null;
            }
        }

        Collections.reverse(collectedEntries);

        String open;
        String close;

        PrettyPrintLayouter pp = prettyPrintVisitor.getPrinter();

        // The base case symbol decides on the
        if (fs.equals(BuiltinSymbols.EMPTY_SET)) {
            open = "{";
            close = "}";
        } else if (fs.equals(BuiltinSymbols.SEQ_EMPTY)) {
            open = "[";
            close = "]";
        } else if (fs.equals(BuiltinSymbols.EMPTY_MULTI_SET)) {
            open = "multiset{";
            close = "}";
        } else {
            prettyPrintVisitor.printApplication(application);
            return;
        }

        pp.append(open);
        int size = collectedEntries.size();
        for (int i = 0; i < size; i++) {
            int[] subsels = new int[size - i];
            for (int j = 0; j < size - i - 1; j++) {
                subsels[j] = 1;
            }
            pp.beginTerm(subsels);
            collectedEntries.get(i).accept(prettyPrintVisitor, null);
            pp.endTerm();

            if (i != size - 1) {
                pp.append(", ");
            }
        }
        pp.append(close);

    }
}
