package edu.kit.iti.algover;

import java.io.FileInputStream;
import java.io.InputStream;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;

import edu.kit.iti.algover.parser.PseudoLexer;
import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoParser.program_return;
import edu.kit.iti.algover.parser.PseudoTree;
import edu.kit.iti.algover.smt.Z3Solver;

import java.io.*;

public class Main {
    private static void test(InputStream stream) throws Exception {
        // create the lexer attached to stream
        ANTLRInputStream input = new ANTLRInputStream(stream);

        PseudoLexer lexer = new PseudoLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        PseudoParser parser = new PseudoParser(tokens);
        parser.setTreeAdaptor(new PseudoTree.Adaptor());
        // launch the parser starting at rule r, get return object
        program_return result = parser.program();
        // pull out the tree and cast it
        PseudoTree t = result.getTree();
        System.out.println(t.toStringTree()); // print out the tree

        Symbex symbex = new Symbex();
        symbex.symbolicExecution(t);

        for (SymbexState res : symbex.getResults()) {
            System.out.println("------------");
            for (PathCondition pc : res.getPathConditions()) {
                System.out.println("Path condition - " + pc.getType());
                System.out.println("    " + pc.getExpression().toStringTree());
                System.out.println("  Assignment History:");
                System.out.println("    " + pc.getMap().toHistoryString().replace("\n", "\n    "));
                System.out.println("  Aggregated Variable Map: ");
                System.out.println("    " + pc.getMap().toParallelAssignment());
                System.out.println("  Instantiated condition: ");
                System.out.println("    " + pc.getMap().instantiate(pc.getExpression()).toStringTree());
                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
            }
            System.out.println("Proof Obligations - " + res.getProofObligationType());
            for (PseudoTree po : res.getProofObligations()) {
                System.out.println("  " + po.toStringTree());
            }
            System.out.println("  Assignment History:");
            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
            System.out.println("  Aggregated Variable Map: ");
            System.out.println("    " + res.getMap().toParallelAssignment());
            System.out.println("  Instantiated POs: ");
            for (PseudoTree po : res.getProofObligations()) {
                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
            }

            Z3Solver z3 = new Z3Solver();
            System.out.println(z3.createSMTInputput(res));
        }

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

    public static void main(String[] args) throws Exception {
        if(args.length == 0) {
            test(System.in);
        } else {
            test(new FileInputStream(args[0]));
        }
    }
}
