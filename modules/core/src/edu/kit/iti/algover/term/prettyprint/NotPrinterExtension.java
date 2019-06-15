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
import edu.kit.iti.algover.term.FunctionSymbolFamily.InstantiatedFunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.FixOperatorCollection.FixOperatorInfo;

/**
 * Pretty print infix and prefix operators.
 *
 * The information about the available operators and their pretty syntax is obtained
 * from a serialized xml file.
 *
 * @see FixOperatorCollection
 * @see FixOperatorInfo
 *
 * @author mulbrich
 */
public class NotPrinterExtension implements PrettyPrintExtension {

    @Override
    public boolean canPrint(FunctionSymbol fs) {
        return fs == BuiltinSymbols.NOT;
    }

    private boolean isNegatedEquality(ApplTerm application) {
        Term inner = application.getTerm(0);
        if (inner instanceof ApplTerm) {
            ApplTerm innerAppl = (ApplTerm) inner;
            FunctionSymbol innerOp = innerAppl.getFunctionSymbol();
            if(innerOp instanceof InstantiatedFunctionSymbol) {
                InstantiatedFunctionSymbol inst = (InstantiatedFunctionSymbol) innerOp;
                if (inst.getFamily() == BuiltinSymbols.EQ) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int getLeftPrecedence(ApplTerm application) {
        if (isNegatedEquality(application)) {
            return 25;
        } else {
            return 60;
        }
    }

    @Override
    public int getRightPrecedence(ApplTerm application) {
        if (isNegatedEquality(application)) {
            return 25;
        } else {
            return 60;
        }
    }

    @Override
    public void print(ApplTerm application, PrettyPrintVisitor visitor) {

        if (isNegatedEquality(application)) {
            printInfixIneq(application.getTerm(0), visitor);
        } else {
            printPrefix(application, visitor);
        }
    }

    /*
     * Prints a term in prefix way.
     *
     * Possibly insert an extra space if needed, that is if
     * two operators follow directly one another.
     */
    private static void printPrefix(ApplTerm application, PrettyPrintVisitor visitor) {

        assert application.getFunctionSymbol() == BuiltinSymbols.NOT;

        Term subterm = application.getTerm(0);

        PrettyPrintLayouter printer = visitor.getPrinter();

        if (isOperatorChar(printer.getLastCharacter())) {
            printer.append(" ");
        }

        printer.append("!");
        printer.beginTerm(0);
        visitor.setLeftPrecedence(60);
        subterm.accept(visitor, null);
        printer.endTerm();
    }

    /*
     * Prints a term in infix way.
     *
     * The first subterm is visited to be put in parens if the precedence is
     * strictly higher than that of this term.
     *
     * The second subterm is visited to be put in parens if the precedence is
     * at least as high as that of this term.
     *
     * Therefore plus(a,plus(b,c)) is put as a + (b + c)
     * and plus(plus(a,b),c) is put as a + b + c
     *
     * All operators are left associative automatically.
     *
     */
    private static void printInfixIneq(Term application, PrettyPrintVisitor visitor) {
        PrettyPrintLayouter printer = visitor.getPrinter();

        String op = "!=";

        printer.beginBlock(0);
        printer.indentBlock(0, op.length() + 1);
        printer.beginTerm(0);
        visitor.setLeftPrecedence(25);
        application.getTerm(0).accept(visitor, null);
        printer.endTerm();

        printer.breakBlock(1, 0).append(op).append(" ");

        printer.beginTerm(1);
        visitor.setLeftPrecedence(25);
        application.getTerm(1).accept(visitor, null);
        printer.endTerm();
        printer.endBlock();
    }

    /**
     * Checks if a character is an operator char.
     */
    private static boolean isOperatorChar(char c) {
        return "+-<>&|=*/!^@.:".indexOf(c) != -1;
    }
}

