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
 * A ProofVerificationCondition contains all path conditions for a specific verification condition
 * Created by sarah on 10/7/15.
 */
public class ProofVerificationCondition {

    //Displayname, it has to be generated using the pathconditions
    private String Name;

    private List<ProofFormula> proofFormulas;

    // symboltable will initially contain all variable declarations and built in symbols as function symbols
    private SymbolTable symbolTable;

    private TreeTermTranslator termbuilder;
    private SymbexState state;
    private DafnyTree method;
    //possible only one element
    //counter for the ids of ProofFormulas, needs to be read by rules in order to create new PF with appropriate ids
    private int idCounter;
    private ProofNode root;
    private ProofHistory history;
    //no to retriev the right proof obligation (beware it starts counting by 0)
    private int siblingNo;



//OLD will be removed
    private List<DafnyTree> assumptions;
    private List<DafnyTree> toShow;
    private LinkedList<PathConditionElement> pcs;

    /**
     * Constructor for a ProofVerificationCondition
     * @param state
     * @param siblingNo
     */
    public ProofVerificationCondition(SymbexState state, int siblingNo){
        this.siblingNo = siblingNo;
        this.state = state;
        this.idCounter= 1;
        this.symbolTable = makeSymbolTable();
        this.termbuilder = new TreeTermTranslator(symbolTable);
        from(state);
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

        //hier siblingno
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

    /**
     * Old, will be removed
     * @param pcs
     * @param assumptions
     * @param toShow
     * @param state
     * @param method
     */
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


}
