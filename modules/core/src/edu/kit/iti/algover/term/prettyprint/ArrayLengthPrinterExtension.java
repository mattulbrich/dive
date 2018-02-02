package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;

public class ArrayLengthPrinterExtension implements PrettyPrintExtension {
    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
       return getLengthString(functionSymbol) != null;
    }

    private String getLengthString(FunctionSymbol functionSymbol) {
        if (functionSymbol instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol symbol = (InstantiatedFunctionSymbol) functionSymbol;

            FunctionSymbolFamily family = symbol.getFamily();
            if(family == BuiltinSymbols.LEN) {
                return "Length";
            }

            if(family == BuiltinSymbols.LEN0) {
                return "Length0";
            }

            if(family == BuiltinSymbols.LEN1) {
                return "Length1";
            }
        }
        return null;
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
        printer.beginTerm(0);
        application.getTerm(0).accept(visitor, null);
        printer.endTerm();
        printer.append("." + getLengthString(application.getFunctionSymbol()));
        printer.endBlock();
    }
}
