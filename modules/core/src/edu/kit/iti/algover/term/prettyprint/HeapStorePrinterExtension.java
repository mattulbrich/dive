/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.Term;

public class HeapStorePrinterExtension implements PrettyPrintExtension {
    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        if(!(functionSymbol instanceof InstantiatedFunctionSymbol)) {
            return false;
        }

        InstantiatedFunctionSymbol ifs =
                (InstantiatedFunctionSymbol) functionSymbol;
        FunctionSymbolFamily family = ifs.getFamily();

        return  family == BuiltinSymbols.STORE ||
                family == BuiltinSymbols.ARRAY_STORE ||
                family == BuiltinSymbols.ARRAY2_STORE;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        // TODO this is relevant
        return 0;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        // TODO this is relevant
        return 0;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        InstantiatedFunctionSymbol ifs =
                (InstantiatedFunctionSymbol) application.getFunctionSymbol();
        FunctionSymbolFamily family = ifs.getFamily();
        PrettyPrintLayouter printer = visitor.getPrinter();

        Term baseheap = application.getTerm(0);

        printer.beginTerm(0);
        baseheap.accept(visitor, null);
        printer.endTerm();

        printer.append("[");

        if(family == BuiltinSymbols.STORE) {
            Term obj = application.getTerm(1);
            Term field = application.getTerm(2);
            Term value = application.getTerm(3);

            printer.beginTerm(1);
            obj.accept(visitor, null);
            printer.endTerm();

            printer.append(".");

            // TODO do this right! --> HeapSelectionPrinter is similar.
            String fieldStr = field.toString();
            fieldStr = fieldStr.substring(fieldStr.lastIndexOf('$') + 1);
            printer.beginTerm(2);
            printer.append(fieldStr);
            printer.endTerm();

            printer.append(" := ");

            printer.beginTerm(2);
            value.accept(visitor, null);
            printer.endTerm();


        } else {
            visitor.visit(application, null);
        }

        printer.append("]");
    }
}
