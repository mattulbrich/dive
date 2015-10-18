package edu.kit.iti.algover.proof;


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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

/**
 * Created by sarah on 10/7/15.
 */
public class ProofVerificationCondition {


    private String Name;

    private LinkedList<ProofFormula> pvc;
    private SymbolTable symbTable;

    private ImmutableList<PathConditionElement> pcs;
    private LinkedList<DafnyTree> assumptions;
    private TreeTermTranslator termbuilder;
    private VariableMap varMap;
    //posible only one element
    private LinkedList<DafnyTree> toShow;

    private int idCounter;


    public ProofVerificationCondition(SymbexState state, LinkedList<DafnyTree> assumptions, LinkedList<DafnyTree> toShow, VariableMap varMap) {
        this.assumptions = assumptions;
        this.toShow = toShow;
        this.varMap = varMap;
//new Symboltable
//        termbuilder = new TreeTermTranslator(symbTable);
        idCounter= 1;
        buildPVC();

    }


    /**
     * Takes the Symbolic Execution state and transforms it to a verification condition.
     * What happens if condition has more than one post condition formula?
     * Here for each POST a pvc has to be created. Where should that be handeled?
     */
    public void buildPVC(){
        for (DafnyTree assumption : assumptions) {
            //SymbolTable has to be retrieved


         //   ProofFormula form = new ProofFormula(idCounter,termbuilder.build(assumption), "");
            idCounter++;
        }

    }





    //        for (SymbexState res : symbex.getResults()) {
//            System.out.println("------------");
//            for (PathCondition pc : res.getPathConditions()) {
//  //              this.conditions.add(pc);
//                System.out.println("Path condition - " + pc.getType());
//                System.out.println("    " + pc.getExpression().toStringTree());
//                System.out.println("  Assignment History:");
//                System.out.println("    " + pc.getMap().toHistoryString().replace("\n", "\n    "));
//                System.out.println("  Aggregated Variable Map: ");
//                System.out.println("    " + pc.getMap().toParallelAssignment());
//                System.out.println("  Instantiated condition: ");
//                System.out.println("    " + pc.getMap().instantiate(pc.getExpression()).toStringTree());
//                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
//            }
//            System.out.println("Proof Obligations - " + res.getProofObligationType());
//            for (DafnyTree po : res.getProofObligations()) {
//                System.out.println("  " + po.toStringTree());
//            }
//            System.out.println("  Assignment History:");
//            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
//            System.out.println("  Aggregated Variable Map: ");
//            System.out.println("    " + res.getMap().toParallelAssignment());
//            System.out.println("  Instantiated POs: ");
//            for (DafnyTree po : res.getProofObligations()) {
//                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
//            } mehrere möglich
//
//            Z3Solver z3 = new Z3Solver();
//            System.out.println(z3.createSMTInputput(res));
//        }
//
}
