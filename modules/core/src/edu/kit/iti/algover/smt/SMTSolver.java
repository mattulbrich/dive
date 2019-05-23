/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

 import org.antlr.stringtemplate.StringTemplate;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.smt.SExpr.Type;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Util;
import org.antlr.stringtemplate.language.AngleBracketTemplateLexer;

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
     * @throws SMTException
     */
    public String createSMTInput(Collection<Term> formulae) throws IOException, SMTException {

        StringBuilder sb = new StringBuilder();

        sb.append(makePreamble());

        sb.append("; === Declarations ===\n\n");
        for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
            if (!fs.getName().matches("[0-9]+")
                    && SMTTrans.getOperationEntry(fs) == null) {
                sb.append(makeDecl(fs)).append("\n");
                sb.append(makeTyping(fs)).append("\n");
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
        template.setAttribute("fields", collectFields());
        return template.toString();
    }

    private SExpr makeDecl(FunctionSymbol fs) {
        SExpr name = new SExpr("fct$" + fs.getName());

        List<SExpr> argList = Collections.nCopies(fs.getArity(), new SExpr("universe"));
        SExpr args = new SExpr(argList);

        return new SExpr("declare-fun", name, args, new SExpr("universe"));
    }

    private SExpr makeTyping(FunctionSymbol fs) throws SMTException {
        int arity = fs.getArity();
        if (arity > 0) {
            List<SExpr> formalParams = new ArrayList<>();
            List<SExpr> actualParams = new ArrayList<>();
            for (int i = 1; i <= arity; i++) {
                formalParams.add(new SExpr("u" + i, "universe"));
                actualParams.add(new SExpr("u" + i));
            }
            SExpr app = new SExpr("fct$" + fs.getName(), Type.UNIVERSE, actualParams);
            SExpr typing = SMTTrans.typingPredicate(app, fs.getResultSort());
            SExpr quant = new SExpr("forall", new SExpr(formalParams), typing);
            return new SExpr("assert", quant);
        } else {
            SExpr app = new SExpr("fct$" + fs.getName(), Type.UNIVERSE);
            SExpr typing = SMTTrans.typingPredicate(app, fs.getResultSort());
            return new SExpr("assert", typing);
        }
    }

    private List<String> collectFields() {
        ArrayList<String> result = new ArrayList<>();
        for (DafnyClass clss : project.getClasses()) {
            for (DafnyField field : clss.getFields()) {
                result.add(clss.getName() + "::" + field.getName());
            }
        }
        return result;
    }

    public abstract Result solve(Collection<Term> formulae) throws IOException;

    /**
     * The possible results obtained from z3.
     */
    public enum Result {
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