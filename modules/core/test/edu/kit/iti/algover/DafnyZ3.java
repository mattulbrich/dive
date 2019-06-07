/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import java.io.FileInputStream;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.antlr.runtime.Token;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.Debug;
import edu.kit.iti.algover.util.LabelIntroducer;
import edu.kit.iti.algover.util.SymbexUtil;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;

public class DafnyZ3 {

    private static boolean VERBOSE = Boolean.getBoolean("algover.verbose");

    private static void test(InputStream stream) throws Exception {
        // create the lexer attached to stream

        DafnyTree t = DafnyFileParser.parse(stream);

        System.out.println(Debug.prettyPrint(t.toStringTree())); // print out the tree

        t.accept(new LabelIntroducer(), null);

        Project project = TestUtil.mockProject(t);

        BuiltinSymbols symbolTable = new BuiltinSymbols();
        TermBuilder tb = new TermBuilder(symbolTable);

        List<PVC> allPVCs = project.getAllPVCs().getContents();

        for (PVC pvc : allPVCs) {

            if(VERBOSE) {
                System.out.println(SymbexUtil.toString(pvc.getPathThroughProgram()));
            }

            Sequent sequent = pvc.getSequent();

            Z3Solver z3 = new Z3Solver(project, symbolTable);

            List<Term> formulae = new ArrayList<>();
            for (ProofFormula formula : sequent.getAntecedent()) {
                formulae.add(formula.getTerm());
            }
            for (ProofFormula formula : sequent.getSuccedent()) {
                formulae.add(tb.negate(formula.getTerm()));
            }

            if (VERBOSE) {
                String smt = z3.createSMTInput(formulae);
                System.out.println(smt);
            }

            System.out.println(z3.solve(formulae));
        }
    }

    // no loinger required
    private static void collectTo(PVCCollection coll, List<PVC> allPVCs) {
        if (coll.isPVCLeaf()) {
            allPVCs.add(coll.getPVC());
        } else {
            for (PVCCollection child : coll.getChildren()) {
                collectTo(child, allPVCs);
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
