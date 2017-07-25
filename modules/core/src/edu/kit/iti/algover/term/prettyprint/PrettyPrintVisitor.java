/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

import java.util.List;

/**
 * The Class PrettyPrint provides means to pretty print terms while keeping the
 * information about subterms in the resulting string.
 *
 * Parentheses are introduced only where necessary.
 */
class PrettyPrintVisitor implements TermVisitor<Void, Void, RuntimeException> {

    private final PrettyPrint pp;
    private final PrettyPrintLayouter printer;

    private int leftPrecedence = 0;

    public PrettyPrintVisitor(PrettyPrint pp, PrettyPrintLayouter printer) {
        this.pp = pp;
        this.printer = printer;
    }

    // TODO remove me
    private void visitMaybeParen(Term subterm, int precedence) {
        subterm.accept(this, null);
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

        FunctionSymbol function = application.getFunctionSymbol();
        PrettyPrintExtension ppe = pp.getExtensionFor(function);

        if(ppe == null) {
            printApplication(application, function.getName());
        } else {
            int rightPrecedence = ppe.getLeftPrecedence(application);
            boolean isInParens = leftPrecedence > rightPrecedence;
            if(isInParens) {
                printer.append("(");
            }

            ppe.print(application, this);
            leftPrecedence = ppe.getRightPrecedence(application);

            if(isInParens) {
                printer.append(")");
            }
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
        boolean isInParens = leftPrecedence > 0;
        if(isInParens) {
            printer.append("(");
        }

        printer.beginBlock(1);
        printer.append("let ");

        List<Pair<VariableTerm, Term>> assignments = updateTerm.getSubstitutions();
        visit(assignments);

        printer.append(" :: ").//resetPreviousStyle().
            breakBlock(0, PrettyPrintLayouter.DEFAULT_INDENTATION);
        printer.beginTerm(0);
        setLeftPrecedence(0);
        visitMaybeParen(updateTerm.getTerm(0), Integer.MAX_VALUE);
        printer.endTerm();
        printer.endBlock();

        if(isInParens) {
            printer.append(")");
        }

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
                printer.breakBlock(0, 0).append(", ");
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

    public int getLeftPrecedence() {
        return leftPrecedence;
    }

    public void setLeftPrecedence(int leftPrecedence) {
        this.leftPrecedence = leftPrecedence;
    }

}

