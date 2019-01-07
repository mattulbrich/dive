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

/**
 * Pretty print sequence accesses
 *
 * This currently covers the get and update for sequences.
 *
 * Lengths of sequences are covered by {@link ArrayLengthPrinterExtension}.
 *
 * @author Mattias Ulbrich
 */
public class SequencePrinterExtension implements PrettyPrintExtension {

    public boolean canPrint(FunctionSymbol functionSymbol) {
        if(!(functionSymbol instanceof InstantiatedFunctionSymbol)) {
            return false;
        }

        InstantiatedFunctionSymbol ifs =
                (InstantiatedFunctionSymbol) functionSymbol;
        FunctionSymbolFamily family = ifs.getFamily();

        return  family == BuiltinSymbols.SEQ_GET
           /*|| family == BuiltinSymbols.SEQ_UPDATE*/;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        // return a very large number (higher than any in/pre-fix operator)
        return 1000;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        // return a very large number (higher than any in/pre-fix operator)
        return 1000;
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {
        InstantiatedFunctionSymbol ifs =
                (InstantiatedFunctionSymbol) application.getFunctionSymbol();
        FunctionSymbolFamily family = ifs.getFamily();
        PrettyPrintLayouter printer = visitor.getPrinter();

        if(family == BuiltinSymbols.SEQ_GET) {
            Term seq = application.getTerm(0);
            Term index = application.getTerm(1);

            printer.beginTerm(0);
            seq.accept(visitor, null);
            printer.endTerm();

            printer.append("[");
            printer.beginTerm(1);
            index.accept(visitor, null);
            printer.endTerm();
            printer.append("]");

        } else if(family == BuiltinSymbols.SEQ_UPDATE) {
            assert false : "To be implemented";

        } else {
            throw new Error("should not be reached");
        }
    }
}
