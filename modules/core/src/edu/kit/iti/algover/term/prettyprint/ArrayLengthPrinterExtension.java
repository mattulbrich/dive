package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;

/**
 * Pretty print the array length attribute.
 *
 * This currently covers the length of one- and two-dimensional arrays and of sequences.
 *
 * @author Mattias Ulbrich
 */
public class ArrayLengthPrinterExtension implements PrettyPrintExtension {

    /**
     * To be used for precedence: Length binds pretty strongly
     */
    private static final int LENGTH_PRECEDENCE = 1000;

    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
       return getLengthString(functionSymbol) != null;
    }

    private static String getLengthString(FunctionSymbol functionSymbol) {
        if (functionSymbol instanceof InstantiatedFunctionSymbol) {
            InstantiatedFunctionSymbol symbol = (InstantiatedFunctionSymbol) functionSymbol;

            FunctionSymbolFamily family = symbol.getFamily();
            if(family == BuiltinSymbols.LEN || family == BuiltinSymbols.SEQ_LEN) {
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
        return LENGTH_PRECEDENCE;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        return LENGTH_PRECEDENCE;
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
