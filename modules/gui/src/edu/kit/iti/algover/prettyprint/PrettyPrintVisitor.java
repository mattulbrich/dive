/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.prettyprint;

import java.util.List;

import edu.kit.iti.algover.prettyprint.AnnotatedString.Style;
import edu.kit.iti.algover.prettyprint.FixOperatorCollection.FixOperatorInfo;
import edu.kit.iti.algover.project.Assignment;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

/**
 * The Class PrettyPrint provides means to pretty print terms while keeping the
 * information about subterms in the resulting string.
 *
 * Parentheses are introduced only where necessary.
 */
class PrettyPrintVisitor implements TermVisitor<Void, Void, RuntimeException> {

    private final PrettyPrint pp;
    private final PrettyPrintLayouter printer;

    /**
     * Indicator that the current subterm is to be put in parentheses
     */
    private boolean inParens;

    public PrettyPrintVisitor(PrettyPrint pp, PrettyPrintLayouter printer) {
        this.pp = pp;
        this.printer = printer;
    }

    /*
     * Visit a subterm and put it in parens possibly.
     *
     * Parens are included if the subterm's precedence is less than
     * the precedence of the surrounding term
     *
     * If typing is switched on, parentheses are included if the
     * term has a non-maximal precedence, i.e. if it is a prefixed
     * or infixed expression
     */
    private void visitMaybeParen(Term subterm, int precedence) {

        int innerPrecedence = getPrecedence(subterm);
        if (innerPrecedence < precedence) {
            inParens = true;
        }

        subterm.accept(this, null);
    }

    /*
     * Gets the precedence of a term. This is straightforward if it is a fixed term.
     * Then the precedence of the operator is returned.
     *
     * In any other case the precedence is maximal ({@link Integer#MAX_VALUE}
     * This is because every infix and prefix operator binds less than other term
     * constructions (binders, applications, even modalities)
     */
    private int getPrecedence(Term subterm) {

        if (pp.isPrintingFix() && subterm instanceof ApplTerm) {
            ApplTerm appl = (ApplTerm) subterm;
            FixOperatorInfo fix = FixOperatorCollection.get(appl.getFunctionSymbol()
                    .getName());
            if (fix != null) {
                return fix.getPrecedence();
            }
        }

        return Integer.MAX_VALUE;
    }

    /*
     * Prints a term in prefix way.
     *
     * Possibly insert an extra space if needed, that is if
     * two operators follow directly one another.
     */
    private void printPrefix(ApplTerm application, FixOperatorInfo fixOperator) {

        assert application.getFunctionSymbol().getArity() == 1;

        Term subterm = application.getTerm(0);

        if (isOperatorChar(printer.getLastCharacter())) {
            printer.append(" ");
        }

        printer.append(fixOperator.getOp());
        printer.beginTerm(0);
        visitMaybeParen(subterm, fixOperator.getPrecedence());
        printer.endTerm();
    }


    /**
     * Append a name to the output stream.
     *
     * If the plugin mechanism is active, then the registered plugins are
     * queried on a replacement. For instance, generated prefixes can be
     * removed, etc.
     *
     * If a replacement is found, it is printed. If not so, or if plugins are
     * deactivated, the argument is printed.
     *
     * @param name
     *            the name to print or to replace.
     */
    /* package visibile, used in the visitor */
    @Deprecated
    void appendName(String name) {
        printer.append(name);
    }

    // keep this updated with TermParser.jj
    /**
     * Checks if a character is an operator char.
     */
    private boolean isOperatorChar(char c) {
        return "+-<>&|=*/!^@.:".indexOf(c) != -1;
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
    private void printInfix(ApplTerm application, FixOperatorInfo fixOperator) {
        printer.beginBlock(0);
        printer.indentBlock(0, 2);
        printer.beginTerm(0);
        visitMaybeParen(application.getTerm(0), fixOperator.getPrecedence());
        printer.endTerm();

        printer.breakBlock(1, 0).append(fixOperator.getOp()).append(" ");

        printer.beginTerm(1);
        visitMaybeParen(application.getTerm(1), fixOperator.getPrecedence() + 1);
        printer.endTerm();
        printer.endBlock();
    }

    /*
     * print an application in non-operator prefix form.
     */
    private void printApplication(ApplTerm application, String fctname) {
        printer.beginBlock(fctname.length() + 1);
        printer.append(fctname);
        List<Term> subterms = application.getSubterms();
        if (subterms.size() > 0) {
            for (int i = 0; i < subterms.size(); i++) {
                if(i == 0) {
                    printer.append("(");
                }
                else {
                    printer.append(",").breakBlock(1,0);
                }
                printer.beginTerm(i);
                subterms.get(i).accept(this, null);
                printer.endTerm();
            }
            printer.append(")");
        }
        printer.endBlock();
    }

    //
    // Visitors
    //

    @Override
    public Void visit(VariableTerm variable, Void arg) {
        printer.setStyle(Style.VARIABLE);
        printer.append(variable.getName());
        printer.resetPreviousStyle();
        return arg;
    }

    @Override
    public Void visit(QuantTerm binding, Void arg) {
        String bindname = binding.getQuantifier().toString().toLowerCase();
        printer.beginBlock(bindname.length() + 1);
        printer.append("(").append(bindname).append(" ");
        printer.setStyle(Style.VARIABLE);
        printer.append(binding.getBoundVar().getName());
        printer.resetPreviousStyle();

        printer.setStyle(Style.TYPE);
        printer.append(":");
        printer.append(binding.getBoundVar().getSort().toString());
        printer.resetPreviousStyle();

        Term t = binding.getTerm(0);
        printer.append(" :: ");
        printer.beginTerm(0);
        t.accept(this, null);
        printer.endTerm();
        printer.append(")");
        printer.endBlock();

        return arg;
    }

    @Override
    public Void visit(ApplTerm application, Void arg) {
        boolean isInParens = inParens;

        if (isInParens) {
            printer.append("(");
        }

        inParens = false;

        FunctionSymbol function = application.getFunctionSymbol();
        String fctname = function.getName();

        FixOperatorInfo fixOperator = null;
        if (pp.isPrintingFix()) {
            fixOperator = FixOperatorCollection.get(fctname);
        }

        if (fixOperator != null) {
            if (function.getArity() == 1) {
                printPrefix(application, fixOperator);
            } else {
                printInfix(application, fixOperator);
            }
        } else {
            printApplication(application, fctname);
        }

        if (isInParens) {
            printer.append(")");
        }

        return null;
    }

    @Override
    public Void visit(SchemaVarTerm schemaVariable, Void arg) {
        printer.append(schemaVariable.getName());
        return null;
    }

    @Override
    public Void visit(LetTerm updateTerm, Void arg) {
        printer.beginBlock(1);
        printer.append("{ ");

        List<Pair<VariableTerm, Term>> assignments = updateTerm.getSubstitutions();
        visit(assignments);

        printer.append(" }").resetPreviousStyle().
            breakBlock(0, PrettyPrintLayouter.DEFAULT_INDENTATION);
        printer.beginTerm(0);
        visitMaybeParen(updateTerm.getTerm(0), Integer.MAX_VALUE);
        printer.endTerm();
        printer.endBlock();

        return arg;
    }

    // used by AssignmentStatement, UpdateTerm and for text instantiation.
    public void visit(List<Pair<VariableTerm, Term>> assignments) {

        printer.beginBlock(0);
        printer.indentBlock(0, 3);

        List<VariableTerm> receivers = Util.map(assignments, Pair::getFst);
        printer.append(Util.commatize(receivers));

        printer.append(" :=").breakBlock(1, 0);

        for (int i = 0; i < assignments.size(); i++) {
            if(i > 0) {
                printer.breakBlock(1, 0).append(", ");
            }
            printer.beginTerm(i + 1);
            assignments.get(i).getSnd().accept(this, null);
            printer.endTerm();
        }

        printer.endBlock();
    }



    public PrettyPrintLayouter getPrinter() {
        return printer;
    }

}

