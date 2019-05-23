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

public class IfThenElsePrinterExtension implements PrettyPrintExtension {

    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        if (functionSymbol instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol inst = (InstantiatedFunctionSymbol) functionSymbol;
            FunctionSymbolFamily family = inst.getFamily();
            return family == BuiltinSymbols.ITE;
        }
        return false;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        return 0;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        return 0;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        PrettyPrintLayouter printer = visitor.getPrinter();
        printer.beginBlock(0);
        printer.append("if ");

        printer.beginTerm(0);
        visitor.setLeftPrecedence(0);
        application.getTerm(0).accept(visitor, null);
        printer.endTerm();

        printer.breakBlock(1, 0);
        printer.append("then ");

        printer.beginTerm(1);
        visitor.setLeftPrecedence(0);
        application.getTerm(1).accept(visitor, null);
        printer.endTerm();

        printer.breakBlock(1, 0);
        printer.append("else ");

        printer.beginTerm(2);
        visitor.setLeftPrecedence(0);
        application.getTerm(2).accept(visitor, null);
        printer.endTerm();
        printer.endBlock();
    }

}
