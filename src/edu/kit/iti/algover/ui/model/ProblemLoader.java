package edu.kit.iti.algover.ui.model;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexState;

/**
 * Created by sarah on 9/9/15.
 */
public class ProblemLoader {

    public static List<SymbexState> results;
    public static LinkedList<String> getPos() {
        return pos;
    }

    private static LinkedList<String> pos = new LinkedList<String>();

    public static void parse(InputStream stream, Boolean hideDetails) throws Exception {
        // create the lexer attached to stream
        ANTLRInputStream input = new ANTLRInputStream(stream);
        DafnyLexer lexer = new DafnyLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        // launch the parser starting at rule r, get return object
        DafnyParser.program_return result = parser.program();
        // pull out the tree and cast it
        DafnyTree t = result.getTree();
        System.out.println(t.toStringTree()); // print out the tree

        Symbex symbex = new Symbex();

        results = symbex.symbolicExecution(t);

        for (SymbexState res : results) {
            System.out.println("------------");
            for (PathConditionElement pc : res.getPathConditions()) {
                //              this.conditions.add(pc);
                System.out.println("Path condition - " + pc.getType());
                pos.add(pc.getType().toString());
                System.out.println("    " + pc.getExpression().toStringTree());
                if(!hideDetails) {
                    System.out.println("  Assignment History:");
                    System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
                    System.out.println("  Aggregated Variable Map: ");
                    System.out.println("    " + pc.getVariableMap().toParallelAssignment());
                }
                System.out.println("  Instantiated condition: ");
                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
                if(!hideDetails) {
                    System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
                }
            }
            System.out.println("Proof Obligations - " + res.getProofObligationType());
            pos.add(res.getProofObligationType().toString());
            for (DafnyTree po : res.getProofObligations()) {
                System.out.println("  " + po.toStringTree());
            }
            if(!hideDetails) {
                System.out.println("  Assignment History:");
                System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
                System.out.println("  Aggregated Variable Map: ");
                System.out.println("    " + res.getMap().toParallelAssignment());
            }
            System.out.println("  Instantiated POs: ");
            for (DafnyTree po : res.getProofObligations()) {
                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
            }

            Z3Solver z3 = new Z3Solver(new ProgramDatabase(t));
            if(!hideDetails) {
            //    System.out.println(z3.createSMTInputput(res));
            }
            //System.out.println(z3.solve(res));
        }




//        // create the lexer attached to stream
//        ANTLRInputStream input = new ANTLRInputStream(stream);
//
//        PseudoLexer lexer = new PseudoLexer(input);
//        // create the buffer of tokens between the lexer and parser
//        CommonTokenStream tokens = new CommonTokenStream(lexer);
//        // create the parser attached to the token buffer
//        PseudoParser parser = new PseudoParser(tokens);
//        parser.setTreeAdaptor(new PseudoTree.Adaptor());
//        // launch the parser starting at rule r, get return object
//        PseudoParser.program_return result = parser.program();
//        // pull out the tree and cast it
//        PseudoTree t = (PseudoTree) result.getTree();
//        System.out.println(t.toStringTree()); // print out the tree
//
//        Symbex symbex = new Symbex();
//        List<SymbexState> results = symbex.symbolicExecution(t);
//
//        for (SymbexState res : results) {
//            System.out.println("------------");
//            for (PathConditionElement pc : res.getPathConditions()) {
//                //              this.conditions.add(pc);
//                System.out.println("Path condition - " + pc.getType());
//                System.out.println("    " + pc.getExpression().toStringTree());
//                System.out.println("  Assignment History:");
//                System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
//                System.out.println("  Aggregated Variable Map: ");
//                System.out.println("    " + pc.getVariableMap().toParallelAssignment());
//                System.out.println("  Instantiated condition: ");
//                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
//                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
//            }
//            System.out.println("Proof Obligations - " + res.getProofObligationType());
//            pos.add(res.getProofObligationType().toString());
//            for (PseudoTree po : res.getProofObligations()) {
//                System.out.println("  " + po.toStringTree());
//            }
//            System.out.println("  Assignment History:");
//            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
//            System.out.println("  Aggregated Variable Map: ");
//            System.out.println("    " + res.getMap().toParallelAssignment());
//            System.out.println("  Instantiated POs: ");
//            for (PseudoTree po : res.getProofObligations()) {
//                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
//            }
//
//            //Z3Solver z3 = new Z3Solver(new ProgramDatabase(t));
//            //System.out.println(z3.createSMTInputput(res));
//        }

    }

//    public static void readFile(File file) {
//        try {
//            FileInputStream inputStream = new FileInputStream(file);
//            parse(inputStream, false);
//
//
//        } catch (FileNotFoundException e) {
//            System.out.println("Could not read file " + file.getAbsolutePath());
//        } catch (Exception e) {
//            System.out.println("Could not load problem");
//            e.printStackTrace();
//        }
//
//    }

    public static void readFile(File file) {

        try {
            FileInputStream inputStream = new FileInputStream(file);
            parse(inputStream, false);


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            System.out.println("Could not load problem");
            e.printStackTrace();
        }

    }

    public static void main(String[] args) throws Exception {
        if(args.length == 0) {
            parse(System.in, true);
        } else {
            parse(new FileInputStream(args[0]), true);
        }
    }
}
