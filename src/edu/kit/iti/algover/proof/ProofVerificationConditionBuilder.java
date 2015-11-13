package edu.kit.iti.algover.proof;


import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.IncrementalSymbolTable;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
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
 * A ProofVerificationConditionBuilder contains all path conditions for a specific verification condition
 * Created by sarah on 10/7/15.
 */
public class ProofVerificationConditionBuilder {

    //Displayname, it has to be generated using the pathconditions
    private String Name;

    private List<ProofFormula> proofFormulas;

    // symboltable will initially contain all variable declarations and built in symbols as function symbols
    private SymbolTable symbolTable;


    private SymbexState state;
    private DafnyTree method;

    /**
     * Returns current counter for a Proof Verification Condition
     * @return
     */
    public int getIdCounter() {
        return idCounter;
    }

    /**
     * Sets the counter for the ProofFormulas. Has to be increased every time a new ProofFormula for this PVC will be created
     * TODO Make sure the proofCenter knows about teh counter
     * @param idCounter
     */
    public void setIdCounter(int idCounter) {
        this.idCounter = idCounter;
    }

    //possible only one element
    //counter for the ids of ProofFormulas, needs to be read by rules in order to create new PF with appropriate ids
    private int idCounter;
    private ProofNode root;
    private ProofHistory history;
    //no to retrieve the right proof obligation (beware it starts counting by 0)
    private int siblingNo;



//OLD will be removed
    private List<DafnyTree> assumptions;
    private List<DafnyTree> toShow;
    private LinkedList<PathConditionElement> pcs;

    /**
     * Constructor for a ProofVerificationConditionBuilder
     * @param state
     * @param siblingNo
     */
    public ProofVerificationConditionBuilder(SymbexState state, int siblingNo){
        this.siblingNo = siblingNo;
        this.state = state;
        //initialize counter for the ProofFormulas in the PVC view
        this.idCounter= 1;
        //symboltable for the PVC to translate DafnyTrees to Terms
        this.method = state.getMethod();
        this.symbolTable = makeSymbolTable();
        extendSymbolTable();
        //create the ProofFormulas
        proofFormulas = translate();
        for (ProofFormula proofFormula : proofFormulas) {
            System.out.println(proofFormula.toString());
        }
        //initialize history
        this.history = createHistory();

        //create root node for proof tree for this PVC
        this.root = buildRoot();


    }

    private void extendSymbolTable() {
        for(PathConditionElement pce : state.getPathConditions()) {
            extendSymbolTable(pce.getInstantiatedExpression());
        }
        for (DafnyTree po : state.getProofObligations()) {
            DafnyTree instantiate = state.getMap().instantiate(po);
            System.out.println(instantiate.toStringTree());
            extendSymbolTable(instantiate);
        }
    }

    /**
     * Create a new ProofFormula and raise idCounter
     * @param t
     * @return
     */
    private ProofFormula makeProofFormula(Term t, String label){
        ProofFormula new_Formula = new ProofFormula(this.idCounter, t, label);
        idCounter++;
        return new_Formula;
    }

    /**
     * Quick and Dirty Solution to find label of tree, better have a more general solution independent of tree structure
     * @param t
     * @return
     */
    private String extractLabel(DafnyTree t){
        String label = "";
        if(t.getChild(0).getType()== DafnyParser.LABEL){
            label = t.getChild(0).getChild(0).getText();
        }

        return label;
    }
    /**
     *
     */
    private List<ProofFormula> translate() {
        List<ProofFormula> all_formulas = new ArrayList<>();

        TreeTermTranslator termbuilder = new TreeTermTranslator(symbolTable);

        for(PathConditionElement pce : state.getPathConditions()) {
            VariableMap map = pce.getVariableMap();
            DafnyTree instantiated_pathcondition = map.instantiate(pce.getExpression());
            Term formula = termbuilder.build(instantiated_pathcondition);
            all_formulas.add(makeProofFormula(formula, extractLabel(instantiated_pathcondition)));


        }

        DafnyTree proof_obligation = extractProofObligation(state.getProofObligations());
        VariableMap map = this.state.getMap();
        DafnyTree instantiated_proofobligation = map.instantiate(proof_obligation.getLastChild());
        Term proof_obligation_Term = termbuilder.build(instantiated_proofobligation);


        //TODO Remove negation: negation should only be done for Z3 solver
        all_formulas.add(makeProofFormula(proof_obligation_Term, extractLabel(instantiated_proofobligation)));

//       result.add(TermBuilder.negate(formula));
//       }
        return all_formulas;
    }

    /**
     * In the future this method may return more than one proof obligation, depending on our decision
     * @param proof_obligations
     * @return
     */
    private DafnyTree extractProofObligation(ImmutableList<DafnyTree> proof_obligations) {
        if(proof_obligations.size() < siblingNo){
            System.out.println("Number of Proofobligation too small: "+proof_obligations.size());
            return null;
        }else{
            Iterator<DafnyTree> iter = proof_obligations.iterator();
            int tempIndex = 0;
            while(iter.hasNext()){
                if(tempIndex == siblingNo){
                    return iter.next();
                }else{
                    iter.next();
                    tempIndex++;
                }
            }
            return null;
        }

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

    private void extendSymbolTable(DafnyTree instantiatedExpression) {

        int type = instantiatedExpression.getType();

        //if we have bound variables
//        if(type == DafnyParser.ALL || type == DafnyParser.EX){
//
//            Sort sort = treeToType(instantiatedExpression.getChild(1));
//            symbolTable = symbolTable.addFunctionSymbol(new FunctionSymbol(instantiatedExpression.getChild(0).toStringTree(), sort));
//        }
        if(type == DafnyParser.ID && instantiatedExpression.getParent().getType() != DafnyParser.LABEL) {
            String name = instantiatedExpression.getText();
            if(name.contains("#")) {
                FunctionSymbol symbol = symbolTable.getFunctionSymbol(name);
                if(symbol == null) {
                    // if we have variables that have a suffix
                    String baseName = name.substring(0, name.indexOf('#'));
                    symbol = symbolTable.getFunctionSymbol(baseName);
                    if (symbol == null) {
                        throw new RuntimeException("Unknown base symbol " + baseName + " for " + name /*, instantiatedExperession*/);
                    }
                    symbolTable = symbolTable.addFunctionSymbol(new FunctionSymbol(name, symbol.getResultSort(), symbol.getArgumentSorts()));
                }
            }
        }


        List<DafnyTree> children = instantiatedExpression.getChildren();
        if(children != null) {
            for (DafnyTree child : children) {
                extendSymbolTable(child);
            }
        }

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
            Term formula = ttt.build(state.getMap().instantiate(po));
            System.out.println(" Formula: "+formula.toString());
            result.add(TermBuilder.negate(formula));
        }

        return result;

    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }






    /**
     * Old, will be removed
     * @param pcs
     * @param assumptions
     * @param toShow
     * @param state
     * @param method
     */
    public ProofVerificationConditionBuilder(LinkedList<PathConditionElement> pcs, LinkedList<DafnyTree> assumptions, LinkedList<DafnyTree> toShow, SymbexState state,
                                             DafnyTree method) {
        this.assumptions = assumptions;
        this.toShow = toShow;
        this.state = state;
        this.pcs = pcs;
        this.method=method;
        this.symbolTable = makeSymbolTable();
       // this.termbuilder = new TreeTermTranslator(symbolTable);

        idCounter= 1;
        from(state);
        //buildPVC();
        this.history = createHistory();
        this.root = buildRoot();

    }


}
