/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Collection;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.Term;

/**
 * Z3 solver can be used to test a collection of terms for satisfiability.
 *
 * @author Mattias Ulbrich
 */
public class Z3Solver extends SMTSolver {

    /**
     * The command by which z3 is invoked.
     */
    public static final String COMMAND =
            System.getProperty("edu.kit.iti.algover.z3_binary", "z3");

    /**
     * Instantiates a new z3 solver.
     *
     * @param symbolTable
     *            the non-<code>null</code> symbol table to use
     */
    public Z3Solver(Project project, SymbolTable symbolTable) {
        super(project, symbolTable);
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

            out.write(createSMTInput(formulae).getBytes());
            out.write("(check-sat)".getBytes());
            out.close();

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while((line = br.readLine()) != null) {
                switch(line) {
                    case "unsat":
                        return Result.UNSAT;
                    case "sat":
                        return Result.SAT;
                    case "unknown":
                        return Result.UNKNOWN;
                }
                System.err.println("Z3: " + line);
            }

            return Result.ERROR;
        } catch (SMTException ex) {
            throw new IOException(ex);
        } finally {
            process.destroy();
        }
    }

    /*
     * Start z3.
     *
     * Add parameters here ...
     */
    private Process buildProcess() throws IOException {
        ProcessBuilder pb = new ProcessBuilder(COMMAND, "-T:3", "-in", "-smt2");
        return pb.start();
    }
}
