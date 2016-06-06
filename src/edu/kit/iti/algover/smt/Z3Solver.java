/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Util;

/**
 * Z3 solver can be used to test a collection of terms for satisfiability.
 *
 * @author Mattias Ulbrich
 */
public class Z3Solver {

    /**
     * The command by which z3 is invoked.
     */
    public static final String COMMAND =
            System.getProperty("edu.kit.iti.algover.z3_binary", "z3");

    /**
     * That is the SMT declarations and defintions to be sent before the
     * translation is sent to Z3.
     */
    private static final String SMT_PREAMBLE;
    static {
        String result;
        try(InputStream is = Z3Solver.class.getResourceAsStream("preamble.smt2")) {
            result = Util.streamToString(is);
        } catch (Exception e) {
            e.printStackTrace();
            result = "; MISSING PREAMBLE\n";
        }
        SMT_PREAMBLE = result;
    }

    /**
     * The possible results obtained from z3.
     */
    enum Result {
        /** The input is unsatisfiable. */
        UNSAT,
        /** The satisfiability status of the input is unknown. */
        UNKNOWN,
        /** The input is satisfiable. */
        SAT,
        /** Indicates that an error has occurred when invoking the solver */
        ERROR
    }

    /**
     * The translation used to SMT-ify terms.
     */
    private final SMTTrans smtTrans = new SMTTrans();

    /**
     * The symbol table to look up logical symbols.
     */
    private SymbolTable symbolTable;

    /**
     * Instantiates a new z3 solver.
     *
     * @param symbolTable
     *            the non-<code>null</code> symbol table to use
     */
    public Z3Solver(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    /**
     * Solve a list of formula by presenting it to the SMT solver.
     *
     * @param formulae
     *            the non-<code>null</code> set of formulae
     * @return the non-<code>null</code> result returned by Z3
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public Result solve(Collection<Term> formulae) throws IOException {

        Process process = buildProcess();
        try {
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            out.write(SMT_PREAMBLE.getBytes());
            out.write(createSMTInput(formulae).getBytes());
            out.close();

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while((line = br.readLine()) != null) {
//                System.err.println("Z3: " + line);
                switch(line) {
                case "unsat":
                    return Result.UNSAT;
                case "sat":
                    return Result.SAT;
                case "unkown":
                    return Result.UNKNOWN;
                }
            }

            return Result.ERROR;
        } finally {
            process.destroy();
        }
    }

    /**
     * Creates smt input to be sent to Z3.
     *
     * This method is separate mainly for testing reasons.
     *
     * @param formulae
     *            the non-<code>null</code> set of formulae to analyse
     * @return the string representation for the formulae
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     */
    public String createSMTInput(Collection<Term> formulae) throws IOException {

        StringBuilder sb = new StringBuilder();

        sb.append("; Declarations \n\n");
        for (FunctionSymbol fs: symbolTable.getAllSymbols()) {
            if(!fs.getName().contains("$") && !fs.getName().matches("[0-9]+")) {
                sb.append(makeDecl(fs)).append("\n");
            }
        }

        sb.append("\n; Proof verification condition\n");

        for (Term pc : formulae) {
            sb.append("; Formula " + pc + "\n");

            sb.append("(assert ");
            sb.append(smtTrans.trans(pc));
            sb.append(")\n\n");
        }
        sb.append("(check-sat)\n");

        return sb.toString();
    }

    /*
     * Make a declaration from a function symbol
     */
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

    /*
     * Start z3.
     *
     * Add parameters here ...
     */
    private Process buildProcess() throws IOException {
        ProcessBuilder pb = new ProcessBuilder(COMMAND, "-t:20", "-in", "-smt2");
        return pb.start();
    }
}
