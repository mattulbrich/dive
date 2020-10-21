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

public class HeapSelectionPrinterExtension implements PrettyPrintExtension {
    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        if(!(functionSymbol instanceof InstantiatedFunctionSymbol)) {
            return false;
        }

        InstantiatedFunctionSymbol ifs =
                (InstantiatedFunctionSymbol) functionSymbol;
        FunctionSymbolFamily family = ifs.getFamily();

        return  family == BuiltinSymbols.SELECT ||
                family == BuiltinSymbols.ARRAY_SELECT /*||
                family == BuiltinSymbols.ARRAY2_SELECT*/;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        // this is more than the arithmetic operations, but less than plain suffix operations
        return 70;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        // this is more than the arithmetic operations, but less than plain suffix operations
        return 70;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        InstantiatedFunctionSymbol ifs =
                (InstantiatedFunctionSymbol) application.getFunctionSymbol();
        FunctionSymbolFamily family = ifs.getFamily();
        PrettyPrintLayouter printer = visitor.getPrinter();

        if(family == BuiltinSymbols.SELECT) {
            Term obj = application.getTerm(1);
            Term field = application.getTerm(2);
            Term heap = application.getTerm(0);

            printer.beginTerm(1);
            obj.accept(visitor, null);
            printer.endTerm();

            printer.append(".");

            // TODO do this right!
            String fieldStr = field.toString();
            fieldStr = fieldStr.substring(fieldStr.lastIndexOf('$') + 1);
            printer.beginTerm(2);
            printer.append(fieldStr);
            printer.endTerm();


            if(heap instanceof ApplTerm &&
                    ((ApplTerm)heap).getFunctionSymbol() == BuiltinSymbols.HEAP) {
                // do not print
            } else {
                //printer.append("@");

                //printer.beginTerm(0);
                //heap.accept(visitor, null);
                //printer.endTerm();
            }

        } else if(family == BuiltinSymbols.ARRAY_SELECT) {
            Term heap = application.getTerm(0);
            Term array = application.getTerm(1);
            Term index = application.getTerm(2);

            printer.beginTerm(1);
            array.accept(visitor, null);
            printer.endTerm();

            printer.append("[");
            printer.beginTerm(2);
            index.accept(visitor, null);
            printer.endTerm();
            printer.append("]");

            if (heap instanceof ApplTerm &&
                    ((ApplTerm) heap).getFunctionSymbol() == BuiltinSymbols.HEAP) {
                // do not print
            } else {
                printer.append("@");

                printer.beginTerm(0);
                heap.accept(visitor, null);
                printer.endTerm();
            }

        } else {
            throw new Error("should not be reached");
        }
    }
}
