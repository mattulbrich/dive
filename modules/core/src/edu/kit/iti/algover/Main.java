/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Debug;
import edu.kit.iti.algover.util.LabelIntroducer;
import edu.kit.iti.algover.util.SymbexUtil;
import edu.kit.iti.algover.util.Util;
import org.antlr.runtime.Token;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

public class Main {

    private static boolean VERBOSE = true;

    private static void test(InputStream stream) throws Exception {
        // create the lexer attached to stream

        DafnyTree t = DafnyFileParser.parse(stream);

        String stringTree = t.toStringTree();
        System.out.println(Debug.prettyPrint(stringTree)); // print out the tree


        LabelIntroducer.visit(t);

        Symbex symbex = new Symbex();
        List<SymbexPath> symbexresult = symbex.symbolicExecution(t);
        //StringBuilder translatedMethod = new StringBuilder();
        String methodName = "";
        for (SymbexPath res : symbexresult) {
            // DafnyTrans dt = new DafnyTrans(res);
            //  String translated = dt.trans();
            // methodName = dt.methodName;
            // translatedMethod.append(translated);

            // TODO M->S: You might want to use the following new method:
            System.out.println("New String:\n\n");
            System.out.println(SymbexUtil.toString(res));

            System.out.println("------------");
            System.out.println(res.getPathIdentifier());
            System.out.println("------------");
            if (VERBOSE) {
                for (PathConditionElement pc : res.getPathConditions()) {
                    System.out.println("Path condition - " + pc.getType());
                    System.out.println("    " + pc.getExpression().toStringTree());
                    System.out.println("  Assignment History:");
                    System.out.println("    " + Util.join(pc.getAssignmentHistory(), "\n    "));
                    System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
                }
                System.out.println("Proof Obligations: ");
                for (AssertionElement po : res.getProofObligations()) {
                    System.out.println("  " + po);
                }

                System.out.println("  Assignment History:");
                System.out.println("    " + Util.join(res.getAssignmentHistory(), "\n    "));
            }

            SymbexStateToFormula magic = new SymbexStateToFormula(t);
//            Z3Solver z3 = new Z3Solver(magic.getSymbolTable());

            for (SymbexPath single : res.split()) {
                System.out.println(single.getPathIdentifier());
                //Collection<Term> formulae = magic.from(single);
                if (VERBOSE) {
                    //    String smt = z3.createSMTInput(formulae);
                    //   System.out.println(smt);
                }
                //System.out.println(z3.solve(formulae));
            }
        }
        //writeOutFile(translatedMethod.toString(), methodName);

    }

    public static void readFile(File file) {
        try {
            FileInputStream inputStream = new FileInputStream(file);
            test(inputStream);


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            System.out.println("Could not load problem");
        }

    }

    public static void writeOutFile(String toProve, String methodName) {
        BufferedWriter writer = null;
        try {
            writer = new BufferedWriter(new FileWriter(methodName + "_toProve.dfy"));
            writer.write(toProve);

        } catch (IOException e) {
        } finally {
            try {
                if (writer != null) {
                    writer.close();
                }
            } catch (IOException e) {
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
                ex.printStackTrace();
            }
        }
    }

}
