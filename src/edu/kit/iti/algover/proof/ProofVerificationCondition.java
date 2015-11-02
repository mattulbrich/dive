package edu.kit.iti.algover.proof;


import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.IncrementalSymbolTable;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexState;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableList;

import javax.xml.transform.sax.SAXSource;
import java.util.*;

/**
 * Created by sarah on 10/7/15.
 */
public class ProofVerificationCondition {


    private String Name;

    private LinkedList<ProofFormula> pvc;

    // symboltable will initially contain all variable declarations and built in symbols as function symbols
    private SymbolTable symbolTable;

   // private ImmutableList<PathConditionElement> pcs;
    private LinkedList<DafnyTree> assumptions;
    private TreeTermTranslator termbuilder;
    private SymbexState state;
    private DafnyTree method;
    //possible only one element
    private LinkedList<DafnyTree> toShow;
    private LinkedList<PathConditionElement> pcs;
    //counter for the ids of ProofFormulas
    private int idCounter;
    private ProofNode root;
    private ProofHistory history;

    public ProofVerificationCondition(LinkedList<PathConditionElement> pcs, LinkedList<DafnyTree> assumptions, LinkedList<DafnyTree> toShow, SymbexState state,
                                       DafnyTree method) {
        this.assumptions = assumptions;
        this.toShow = toShow;
        this.state = state;
        this.pcs = pcs;
        this.method=method;
        this.symbolTable = makeSymbolTable();
        this.termbuilder = new TreeTermTranslator(symbolTable);

        idCounter= 1;
        from(state);
        //buildPVC();
        this.history = createHistory();
        this.root = buildRoot();

    }

    /**
     * Create initial history object, containing all initial proof formulas
     * @return
     */
    private ProofHistory createHistory() {
        return null;
    }

    /**
     * Builds the rootnode for a proof verification condition
     * @return rootnode
     */
    private ProofNode buildRoot() {
        ProofNode root = new ProofNode(null, null, this.history);
        return root;
    }

    /**
     *
     * @return Symboltable containing all variable declarations and builtin function symbols
     * Author: Mattias Ulbrich
     */

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new MapSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    public static Sort treeToType(DafnyTree tree) {
        String name = tree.toString();
        if("array".equals(name)) {
            name = "array1";
        }

        return new Sort(name);
    }

    /**
     * Copied from Mattias, will have own
     * @param symbexState
     * @return
     */
    public Collection<Term> from(SymbexState symbexState) {

        Collection<Term> result = new ArrayList<>();

        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);

        for(PathConditionElement pce : symbexState.getPathConditions()) {
            Term formula = ttt.build(pce.getExpression());
            System.out.println(" Formula: "+formula.toString());
            result.add(formula);
        }

        for(DafnyTree po : symbexState.getProofObligations()) {
            Term formula = ttt.build(po.getLastChild());
            System.out.println(" Formula: "+formula.toString());
            result.add(TermBuilder.negate(formula));
        }

        return result;

    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }




    /**
     * Takes the Symbolic Execution state and transforms it to a verification condition.
     * What happens if condition has more than one post condition formula?
     * Here for each POST a pvc has to be created. Where should that be handeled?
     */
    public void buildPVC(){
        for (DafnyTree assumption : assumptions) {
            ProofFormula form = new ProofFormula(idCounter,termbuilder.build(assumption), "");
            idCounter++;
            System.out.println("Created Terms:"+form.toString() );
        }
       // for(PathConditionElement pce : pcs) {
        //    Term formula = termbuilder.build(pce.getExpression());
         //   System.out.println("Path: "+formula.toString());
        //}
        for (DafnyTree dafnyTree : toShow) {
            ProofFormula form = new ProofFormula(idCounter,termbuilder.build(dafnyTree), "");
            System.out.println("Created Terms:"+form.toString() );
            idCounter++;
        }


    }

}
