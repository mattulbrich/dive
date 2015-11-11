package edu.kit.iti.algover.ui.model;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.ProofOld;
import edu.kit.iti.algover.ProofCenter;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.proof.IllegalStateException;
import edu.kit.iti.algover.smt.Z3Solver;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.CommonTokenStream;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.ProofCenter;
import edu.kit.iti.algover.ProofOld;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexState;

/**
 * Class responsible for loading a problem file, parsing it and performing symbolic execution
 *
 * Created by sarah on 9/9/15.
 */
public class ProblemLoader {
    //list of collected proof obligations
    private static LinkedList<ProofOld> proofList;


    //getters
    public static LinkedList<ProofOld> getProofList() {
        return proofList;
    }

    private File file;
    private static DafnyTree ast;

    private List<DafnyTree> methods;
    private static boolean tempTest = true;
    /**
     * Parse an InputStream
     * @param stream
     * @throws Exception
     */
    private static void parse(InputStream stream) throws Exception {
        ANTLRInputStream input = new ANTLRInputStream(stream);
        DafnyLexer lexer = new DafnyLexer(input);
        ast = buildAST(lexer);
        if(tempTest){
            depr_buildAST(ast);
        }

    }

    /**
     * Parse a BufferedReader input
     * @param reader
     * @throws Exception
     */
    public static void parse(BufferedReader reader) throws Exception {

        ANTLRReaderStream input = new ANTLRReaderStream(reader);
        // create the lexer attached to stream
        DafnyLexer lexer = new DafnyLexer(input);
        ast = buildAST(lexer);
        if(tempTest){
            depr_buildAST(ast);
        }
    }

    /**
     * Perform symbolic execution of a method and create ContractProofObligation
     * @param method
     */
    public ContractProofObligation performSymbEx(DafnyTree method) throws IllegalStateException {

        Symbex symbex = new Symbex();
        List<SymbexState> results = symbex.symbolicExecution(method);

        return new ContractProofObligation(results, method);
    }
    /**
     * Perform symbolic execution of a method and create ContractProofObligation
     *
     * @param name of method
     */
    public ContractProofObligation performSymbEx(String name) throws IllegalStateException {

        return null;
    }

    /**
     * Should list all Methods of a problem file therefore should not be void ;-)
     */
    public List<DafnyTree> listMethods() throws IllegalStateException {
        if (methods != null){
            return methods;
        }else{
            throw new IllegalStateException("The problem file has to be parsed in order to list all methods");
        }

    }

    /**
     * Read and Parse a File
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
    /**
     * Build the AST given the DafnyLexer (old)
     * @param lexer
     * @throws Exception
     */
    private static DafnyTree buildAST(DafnyLexer lexer) throws  Exception {


        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        // launch the parser starting at rule r, get return object
        DafnyParser.program_return result = parser.program();
        // pull out the tree and cast it
        DafnyTree t = result.getTree();
        return t;
    }

    /**
     * Testmethod, will be removed
     * @param t
     * @throws Exception
     */
    private static void depr_buildAST(DafnyTree t) throws  Exception{

        System.out.println(t.toStringTree()); // print out the tree

        Symbex symbex = new Symbex();

        List<SymbexState> results = symbex.symbolicExecution(t);



        //Ab hier ist der Code in CPO verschoben worden, muss noch herausgenommen werden, wenn GUI Elemente angepasst sind.
        ProofCenter pcenter = ProofCenter.getInstance();
        LinkedList<DafnyTree> instantiatedAssumptions;

        LinkedList<PathConditionElement> typeCollectionPath;
        LinkedList<PathConditionElement.AssertionType> typeCollectionState;
        LinkedList<DafnyTree> assumptions;


        proofList = new LinkedList<ProofOld>();

        for (SymbexState res : results) {
            assumptions = new LinkedList<DafnyTree>();
            instantiatedAssumptions  = new LinkedList<DafnyTree>();
            typeCollectionPath = new LinkedList<PathConditionElement>();
            typeCollectionState  = new LinkedList<PathConditionElement.AssertionType>();

           // System.out.println("------------");
            for (PathConditionElement pc : res.getPathConditions()) {
                typeCollectionPath.addLast(pc);
//                System.out.println("Path condition - " + pc.getType());
//                System.out.println("    " + pc.getExpression().toStringTree());
//                System.out.println("  Assignment History:");
//                System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
//                System.out.println("  Aggregated Variable Map: ");
//                System.out.println("    " + pc.getVariableMap().toParallelAssignment());
//                System.out.println("  Instantiated condition: ");
                assumptions.add(pc.getExpression());
                instantiatedAssumptions.add(pc.getVariableMap().instantiate(pc.getExpression()));
//                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
//                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
//                System.out.println("  Test Line: " + pc.getExpression());
            }


//            System.out.println("Proof Obligations - " + res.getProofObligationType());
            typeCollectionState.add(res.getProofObligationType());
//            for (DafnyTree po : res.getProofObligations()) {
      //          LinkedList<DafnyTree> toShow = new LinkedList<DafnyTree>();
      //          toShow.add(res.getMap().instantiate(po));
      //          ProofOld p = pcenter.createProofOldObject(res, assumptions, toShow, typeCollectionPath, typeCollectionState, 0);
      //          pcenter.insertProofOld(p);
//                System.out.println(po.childIndex);
//                System.out.println("  " + po.toStringTree());
//            }


//            System.out.println("  Assignment History:");
//            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
//            System.out.println("  Aggregated Variable Map: ");
//            System.out.println("    " + res.getMap().toParallelAssignment());
//            System.out.println("  Instantiated POs: ");
//            System.out.println("No of PO: "+ res.getProofObligations().size());

            for (DafnyTree po : res.getProofObligations()) {
                //System.out.println("Sibling: "+po.+"\n\n\n");

                LinkedList<DafnyTree> toShow = new LinkedList<DafnyTree>();
                toShow.add(res.getMap().instantiate(po));
                ProofOld p = pcenter.createProofOldObject(res, instantiatedAssumptions, toShow, typeCollectionPath, typeCollectionState, 0);
                pcenter.insertProofOld(p);
//                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
            }



        }
    }


}