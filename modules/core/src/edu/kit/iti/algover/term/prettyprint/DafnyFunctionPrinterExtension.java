/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;

import java.util.List;

/**
 * Pretty print Dafny function applications.
 *
 * If the function is not defined within a class, then the occurrence
 * {@code $$f(heap, args)} is translated to {@code f(args)@heap}.
 *
 * If the function is defined within a class, then the occurrence
 * {@code $$f(heap, receiver, args)} is translated to
 * {@code receiver.f(args)@heap}.
 *
 * If the heap is the initial heap, then "@heap" is ommited.
 *
 * @author Mattias Ulbrich
 */
public class DafnyFunctionPrinterExtension implements PrettyPrintExtension {

    @Override
    public boolean canPrint(FunctionSymbol functionSymbol) {
        return functionSymbol instanceof DafnyFunctionSymbol;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        // TODO
        return 1000;
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        // TODO
        return 1000;
    }

    @Override
    public void print(ApplTerm term, PrettyPrintVisitor ppv) {

        FunctionSymbol functionSymbol = term.getFunctionSymbol();
        assert functionSymbol instanceof DafnyFunctionSymbol :
                "This extension is only applicable to DafnyFunctions";

        DafnyFunctionSymbol fs = (DafnyFunctionSymbol) functionSymbol;
        DafnyFunction f = fs.getOrigin();
        PrettyPrintLayouter printer = ppv.getPrinter();

        printer.beginBlock(4);
        int firstArg = 1;
        if (f.isDeclaredInClass()) {
            printer.beginTerm(1);
            term.getTerm(1).accept(ppv, null);
            printer.endTerm();
            firstArg = 2;
            printer.append(".");
        }

        List<Term> subterms = term.getSubterms();
        printer.setStyle(Style.USER_ENTITY);
        printer.append(f.getName());
        printer.resetPreviousStyle();

        printer.append("(");

        for (int i = firstArg; i < subterms.size(); i++) {
            if(i != firstArg) {
               printer.append(",").breakBlock(1,0);
            }
            printer.beginTerm(i);
            subterms.get(i).accept(ppv, null);
            printer.endTerm();
        }
        printer.append(")");

        Term heap = subterms.get(0);
        if (heap instanceof ApplTerm &&
                ((ApplTerm)heap).getFunctionSymbol() == BuiltinSymbols.HEAP) {
            // do not print
        } else {
            printer.append("@");

            printer.beginTerm(0);
            heap.accept(ppv, null);
            printer.endTerm();
        }

        printer.endBlock();

    }

}
