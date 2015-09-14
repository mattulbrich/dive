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
    public static LinkedList<String> getPos() {
        return pos;
    }

    private static LinkedList<String> pos = new LinkedList<String>();

    private static void parse(InputStream stream) throws Exception {

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
        List<SymbexState> results = symbex.symbolicExecution(t);

        for (SymbexState res : results) {
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
            pos.add(res.getProofObligationType().toString());
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

//            Z3Solver z3 = new Z3Solver(new ProgramDatabase(t));
//            System.out.println(z3.createSMTInputput(res));
        }

    }

    public static void readFile(File file) {
        try {
            FileInputStream inputStream = new FileInputStream(file);
        try {
            FileInputStream inputStream = new FileInputStream(file);
            parse(inputStream);
        } catch (FileNotFoundException e) {
            e.printStackTrace();
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            e.printStackTrace();
            System.out.println("Could not load problem");
        }

    }

    public static void main(String[] args) throws Exception {
        if(args.length == 0) {
            parse(System.in);
        } else {
            parse(new FileInputStream(args[0]));
        }
    }
}