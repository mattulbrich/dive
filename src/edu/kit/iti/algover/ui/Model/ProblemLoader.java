package edu.kit.iti.algover.ui.Model;

import edu.kit.iti.algover.PathCondition;
import edu.kit.iti.algover.Symbex;
import edu.kit.iti.algover.SymbexState;
import edu.kit.iti.algover.parser.PseudoLexer;
import edu.kit.iti.algover.parser.PseudoParser;
import edu.kit.iti.algover.parser.PseudoTree;
import edu.kit.iti.algover.smt.Z3Solver;
import javafx.collections.ObservableList;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.LinkedList;

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

        PseudoLexer lexer = new PseudoLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        PseudoParser parser = new PseudoParser(tokens);
        parser.setTreeAdaptor(new PseudoTree.Adaptor());
        // launch the parser starting at rule r, get return object
        PseudoParser.program_return result = parser.program();
        // pull out the tree and cast it
        PseudoTree t = result.getTree();
        System.out.println(t.toStringTree()); // print out the tree

        Symbex symbex = new Symbex();
        symbex.symbolicExecution(t);

        for (SymbexState res : symbex.getResults()) {
            System.out.println("------------");
            for (PathCondition pc : res.getPathConditions()) {
                //              this.conditions.add(pc);
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
            pos.add(res.getProofObligationType().toString());
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
            parse(inputStream);


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
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
