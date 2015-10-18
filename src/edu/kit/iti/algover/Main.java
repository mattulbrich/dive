package edu.kit.iti.algover;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.List;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.program_return;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexState;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Debug;

public class Main {

    private static void test(InputStream stream) throws Exception {
        // create the lexer attached to stream
      ANTLRInputStream input = new ANTLRInputStream(stream);


        DafnyLexer lexer = new DafnyLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        // launch the parser starting at rule r, get return object
        program_return result;
        try {
            result = parser.program();
        } catch (RecognitionException e) {
            throw new Exception(parser.getErrorHeader(e) + ": " + parser.getErrorMessage(e, parser.getTokenNames()), e);
        }
        // pull out the tree and cast it
        DafnyTree t = result.getTree();
        String stringTree = t.toStringTree();
        System.out.println(Debug.prettyPrint(stringTree)); // print out the tree

        Symbex symbex = new Symbex();
        List<SymbexState> symbexresult = symbex.symbolicExecution(t);

        for (SymbexState res : symbexresult) {
            System.out.println("------------");
            for (PathConditionElement pc : res.getPathConditions()) {
  //              this.conditions.add(pc);
                System.out.println("Path condition - " + pc.getType());
                System.out.println("    " + pc.getExpression().toStringTree());
                System.out.println("  Assignment History:");
                System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
                System.out.println("  Aggregated Variable Map: ");
                System.out.println("    " + pc.getVariableMap().toParallelAssignment());
                System.out.println("  Instantiated condition: ");
                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
            }
            System.out.println("Proof Obligations - " + res.getProofObligationType());
            for (DafnyTree po : res.getProofObligations()) {
                System.out.println("  " + po.toStringTree());
            }
            System.out.println("  Assignment History:");
            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
            System.out.println("  Aggregated Variable Map: ");
            System.out.println("    " + res.getMap().toParallelAssignment());
            System.out.println("  Instantiated POs: ");
            for (DafnyTree po : res.getProofObligations()) {
                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
            }

            SymbexStateToFormula magic = new SymbexStateToFormula(t);

            Z3Solver z3 = new Z3Solver(magic.getSymbolTable());
            String smt = z3.createSMTInputput(magic.from(res));
            System.out.println(Debug.prettyPrint(smt));
            System.out.println(smt);

            System.out.println(z3.solve(magic.from(res)));
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
//        DafnyLexer lexer = new DafnyLexer(input);
//        // create the buffer of tokens between the lexer and parser
//        CommonTokenStream tokens = new CommonTokenStream(lexer);
//        // create the parser attached to the token buffer
//        DafnyParser parser = new DafnyParser(tokens);
//        parser.setTreeAdaptor(new DafnyTree.Adaptor());
//        // launch the parser starting at rule r, get return object
//        program_return result = parser.program();
//        // pull out the tree and cast it
//        DafnyTree t = result.getTree();
//        System.out.println(t.toStringTree()); // print out the tree
//
//        Symbex symbex = new Symbex();
//        symbex.symbolicExecution(t);
//
//        for (SymbexState res : symbex.getResults()) {
//            System.out.println("------------");
//            for (PathConditionElement pc : res.getPathConditions()) {
//                System.out.println("Path condition - " + pc.getType());
//                System.out.println("    " + pc.getExpression().toStringTree());
//                if(!hideDetails) {
//                    System.out.println("  Assignment History:");
//                    System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
//                    System.out.println("  Aggregated Variable Map: ");
//                    System.out.println("    " + pc.getVariableMap().toParallelAssignment());
//                }
//                System.out.println("  Instantiated condition: ");
//                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
//                if(!hideDetails) {
//                    System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
//                }
//            }
//            System.out.println("Proof Obligations - " + res.getProofObligationType());
//            for (DafnyTree po : res.getProofObligations()) {
//                System.out.println("  " + po.toStringTree());
//            }
//            if(!hideDetails) {
//                System.out.println("  Assignment History:");
//                System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
//                System.out.println("  Aggregated Variable Map: ");
//                System.out.println("    " + res.getMap().toParallelAssignment());
//            }
//            System.out.println("  Instantiated POs: ");
//            for (DafnyTree po : res.getProofObligations()) {
//                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
//            }
//
//            Z3Solver z3 = new Z3Solver(new ProgramDatabase(t));
//            if(!hideDetails) {
//                System.out.println(z3.createSMTInputput(res));
//            }
//            System.out.println(z3.solve(res));
//        }

//    }
//
//    public static void readFile(File file) {
//        try {
//            FileInputStream inputStream = new FileInputStream(file);
//            test(inputStream, false);
//
//
//        } catch (FileNotFoundException e) {
//            System.out.println("Could not read file " + file.getAbsolutePath());
//        } catch (Exception e) {
//            System.out.println("Could not load problem");
//        }
//
//    }
//
//    public static void main(String[] args) throws Exception {
//        if(args.length == 0) {
//            test(System.in, false);
//        } else {
//            test(new FileInputStream(args[0]), args.length > 1);
//        }
//    }
}
