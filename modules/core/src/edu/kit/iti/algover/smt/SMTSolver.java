/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.smt;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.antlr.stringtemplate.StringTemplate;
import org.antlr.stringtemplate.language.AngleBracketTemplateLexer;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Util;

public abstract class SMTSolver {

    /**
     * That is the SMT declarations and defintions to be sent before the
     * translation is sent to Z3.
     */
    private static final String SMT_PREAMBLE_TEMPLATE;

    static {
        String result;
        try (InputStream is = Z3Solver.class.getResourceAsStream("preamble.smt2")) {
            result = Util.streamToString(is);
        } catch (Exception e) {
            e.printStackTrace();
            result = "; MISSING PREAMBLE\n";
        }
        SMT_PREAMBLE_TEMPLATE = result;
    }

    /**
     * The translation used to SMT-ify terms.
     */
    private final SMTTrans smtTrans = new SMTTrans();
    /**
     * The symbol table to look up logical symbols.
     */
    private final SymbolTable symbolTable;
    private Project project;

    public SMTSolver(Project project, SymbolTable symbolTable) {
        this.project = project;
        this.symbolTable = symbolTable;
    }

    /**
     * Creates smt input to be sent to the solver.
     * <p>
     * This method is separate mainly for testing reasons.
     *
     * @param formulae the non-<code>null</code> set of formulae to analyse
     * @return the string representation for the formulae
     * @throws IOException Signals that an I/O exception has occurred.
     */
    public String createSMTInput(Collection<Term> formulae) throws IOException {

        StringBuilder sb = new StringBuilder();

        sb.append(makePreamble());

        sb.append("; === Declarations ===\n\n");
        for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
            if (!fs.getName().contains("$") && !fs.getName().matches("[0-9]+")) {
                sb.append(makeDecl(fs)).append("\n");
            }
        }

        sb.append("\n; === Proof verification condition ===\n");

        for (Term pc : formulae) {
            sb.append("; --- Formula " + pc + " ---\n");

            sb.append("(assert ");
            sb.append(smtTrans.trans(pc));
            sb.append(")\n\n");
        }
        sb.append("(check-sat)\n");

        return sb.toString();
    }

    private String makePreamble() {
        StringTemplate template = new StringTemplate(SMT_PREAMBLE_TEMPLATE, AngleBracketTemplateLexer.class);
        template.setAttribute("classes", Util.map(project.getClasses(), DafnyDecl::getName));
        // FIXME
        template.setAttribute("fields", Arrays.asList("A::b", "C::d"));
        return template.toString();
    }

    private SExpr makeDecl(FunctionSymbol fs) {
        SExpr name = new SExpr(fs.getName());

        SExpr result = SMTTrans.typeToSMT(fs.getResultSort());

        List<SExpr> argList = new ArrayList<>();
        for (Sort argSort : fs.getArgumentSorts()) {
            argList.add(SMTTrans.typeToSMT(argSort));
        }
        SExpr args = new SExpr(argList);

        return new SExpr("declare-fun", name, new SExpr(args), result);
    }

    public abstract Result solve(Collection<Term> formulae) throws IOException;

    /**
     * The possible results obtained from z3.
     */
    enum Result {
        /**
         * The input is unsatisfiable.
         */
        UNSAT,
        /**
         * The satisfiability status of the input is unknown.
         */
        UNKNOWN,
        /**
         * The input is satisfiable.
         */
        SAT,
        /**
         * Indicates that an error has occurred when invoking the solver
         */
        ERROR
    }
}