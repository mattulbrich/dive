package edu.kit.iti.algover.ui.model;

import java.io.*;
import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.Proof;
import edu.kit.iti.algover.ProofCenter;
import edu.kit.iti.algover.util.ImmutableList;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.CommonTokenStream;

import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexState;

/**
 * Created by sarah on 9/9/15.
 */
public class ProblemLoader {
    //list of collected proof obligations
    private static LinkedList<Proof> proofList;


    //getters
    public static LinkedList<Proof> getProofList() {
        return proofList;
    }



    /**
     * Parse an Inputstream
     * @param stream
     * @throws Exception
     */
    private static void parse(InputStream stream) throws Exception {
        ANTLRInputStream input = new ANTLRInputStream(stream);
        DafnyLexer lexer = new DafnyLexer(input);
        buildAST(lexer);
    }

    /**
     * Parse a bufferedreader input
     * @param reader
     * @throws Exception
     */
    public static void parse(BufferedReader reader) throws Exception {

        ANTLRReaderStream input = new ANTLRReaderStream(reader);
        // create the lexer attached to stream
        DafnyLexer lexer = new DafnyLexer(input);
        buildAST(lexer);
    }

    /**
     * Build the AST given the DafnyLexer
     * @param lexer
     * @throws Exception
     */
    private static void buildAST(DafnyLexer lexer) throws  Exception{
        ProofCenter pcenter = ProofCenter.getInstance();
        LinkedList<DafnyTree> instantiatedAssumptions;

        LinkedList<PathConditionElement> typeCollectionPath;
        LinkedList<PathConditionElement.AssertionType> typeCollectionState;

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
        proofList = new LinkedList<Proof>();

        for (SymbexState res : results) {

            instantiatedAssumptions  = new LinkedList<DafnyTree>();
            typeCollectionPath = new LinkedList<PathConditionElement>();
            typeCollectionState  = new LinkedList<PathConditionElement.AssertionType>();

            System.out.println("------------");
            for (PathConditionElement pc : res.getPathConditions()) {
                typeCollectionPath.addLast(pc);
                System.out.println("Path condition - " + pc.getType());
                System.out.println("    " + pc.getExpression().toStringTree());
                System.out.println("  Assignment History:");
                System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
                System.out.println("  Aggregated Variable Map: ");
                System.out.println("    " + pc.getVariableMap().toParallelAssignment());
                System.out.println("  Instantiated condition: ");
                instantiatedAssumptions.add(pc.getVariableMap().instantiate(pc.getExpression()));
                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
                System.out.println("  Test Line: " + pc.getExpression());
            }


            System.out.println("Proof Obligations - " + res.getProofObligationType());
            typeCollectionState.add(res.getProofObligationType());
            for (DafnyTree po : res.getProofObligations()) {
                System.out.println("  " + po.toStringTree());
            }


            System.out.println("  Assignment History:");
            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
            System.out.println("  Aggregated Variable Map: ");
            System.out.println("    " + res.getMap().toParallelAssignment());
            System.out.println("  Instantiated POs: ");
            for (DafnyTree po : res.getProofObligations()) {
                LinkedList<DafnyTree> toShow = new LinkedList<DafnyTree>();
                toShow.add(res.getMap().instantiate(po));
                Proof p = pcenter.createProofObject(instantiatedAssumptions, toShow, typeCollectionPath, typeCollectionState, 0);
                pcenter.insertProof(p);
                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
            }


//            Z3Solver z3 = new Z3Solver(new ProgramDatabase(t));
//            System.out.println(z3.createSMTInputput(res));
        }
    }

    /**
     * Read an Parse a File
     * @param file
     */
    public static void readFile(File file) {

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