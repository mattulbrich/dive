/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import java.io.FileInputStream;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.List;

import org.antlr.runtime.Token;

import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Debug;
import edu.kit.iti.algover.util.LabelIntroducer;
import edu.kit.iti.algover.util.SymbexUtil;
import edu.kit.iti.algover.util.Util;

public class DafnyZ3 {

    private static boolean VERBOSE = Boolean.getBoolean("algover.verbose");

    private static void test(InputStream stream) throws Exception {
        // create the lexer attached to stream

        DafnyTree t = DafnyFileParser.parse(stream);

        System.out.println(Debug.prettyPrint(t.toStringTree())); // print out the tree

        t.accept(new LabelIntroducer(), null);

        Symbex symbex = new Symbex();
        List<SymbexPath> symbexresult = symbex.symbolicExecution(t);
        for (SymbexPath res : symbexresult) {

            if(VERBOSE) {
               System.out.println(SymbexUtil.toString(res));
            }

            SymbexStateToFormula magic = new SymbexStateToFormula(t);
            Z3Solver z3 = new Z3Solver(magic.getSymbolTable());

            for (SymbexPath single : res.split()) {
                Collection<Term> formulae = magic.from(single);
                if (VERBOSE) {
                    String smt = z3.createSMTInput(formulae);
                    System.out.println(smt);
                }
                System.out.println(single);
                System.out.println(z3.solve(formulae));
            }
        }

    }

    public static void main(String[] args) throws Exception {
        try {
            if (args.length == 0) {
                test(System.in);
            } else {
                test(new FileInputStream(args[0]));
            }
        } catch (TermBuildException ex) {
            DafnyTree location = ex.getLocation();
            if (location != null) {
                Token tok = location.token;
                int pos = tok.getCharPositionInLine();
                int line = tok.getLine();
                List<String> lines = Files.readAllLines(Paths.get(args[0]));
                System.err.println(lines.get(line));
                System.err.println(Util.duplicate(" ", pos) + "^^^");
            }
            ex.printStackTrace();
        }
    }

}
