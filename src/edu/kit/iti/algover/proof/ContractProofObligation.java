package edu.kit.iti.algover.proof;

import com.sun.javafx.collections.ImmutableObservableList;
import edu.kit.iti.algover.ProofCenter;
import edu.kit.iti.algover.ProofOld;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexState;

import java.util.LinkedList;
import java.util.List;

/**
 * This class handles the transformation of the symbolic execution states into ProofVerificationCondition
 * Created by sarah on 10/23/15.
 */
public class ContractProofObligation {
    private List<ProofVerificationCondition> verification_conditions;

    ProofCenter pcenter;

    /**
     * Create all ProofVerificationConditions for a method
     * @param symbex_states
     */
    public ContractProofObligation(List<SymbexState> symbex_states){
        pcenter  = ProofCenter.getInstance();
        createPVC(symbex_states);
    }

    /**
     * This method iterates over all symbolic execution states and creates a ProofVerificationCondition for each
     * Condition and ProofObligation. The method adds each ProofVerificationCondition
     * @param symbex_states
     */
    private void createPVC(List<SymbexState> symbex_states) {
        //maybe I don't need an observable list (atm not sure)
        verification_conditions = new ImmutableObservableList<ProofVerificationCondition>();


        LinkedList<DafnyTree> instantiatedAssumptions;

        LinkedList<PathConditionElement> typeCollectionPath;
        LinkedList<PathConditionElement.AssertionType> typeCollectionState;
        LinkedList<DafnyTree> assumptions;
        //Ab hier muss der Code in CPO verschoben werden


        for (SymbexState res : symbex_states) {
            assumptions = new LinkedList<DafnyTree>();
            instantiatedAssumptions = new LinkedList<DafnyTree>();
            typeCollectionPath = new LinkedList<PathConditionElement>();
            typeCollectionState = new LinkedList<PathConditionElement.AssertionType>();

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
                assumptions.add(pc.getExpression());
                instantiatedAssumptions.add(pc.getVariableMap().instantiate(pc.getExpression()));
                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
                System.out.println("  Test Line: " + pc.getExpression());
            }


            System.out.println("Proof Obligations - " + res.getProofObligationType());
            typeCollectionState.add(res.getProofObligationType());
            for (DafnyTree po : res.getProofObligations()) {
                //          LinkedList<DafnyTree> toShow = new LinkedList<DafnyTree>();
                //          toShow.add(res.getMap().instantiate(po));
                //          ProofOld p = pcenter.createProofOldObject(res, assumptions, toShow, typeCollectionPath, typeCollectionState, 0);
                //          pcenter.insertProofOld(p);
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
                ProofOld p = pcenter.createProofOldObject(res, instantiatedAssumptions, toShow, typeCollectionPath, typeCollectionState, 0);
                pcenter.insertProofOld(p);
                System.out.println("    " + res.getMap().instantiate(po).toStringTree());
            }

        }}
}
