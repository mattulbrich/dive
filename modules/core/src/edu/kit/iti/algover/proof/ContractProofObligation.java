/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.ProofCenter;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;

import java.util.LinkedList;
import java.util.List;

/**
 * This class handles the transformation of the symbolic execution states into ProofVerificationConditionBuilder
 * Created by sarah on 10/23/15.
 */
@Deprecated
public class ContractProofObligation {
    private List<ProofVerificationConditionBuilder> verification_conditions;
    public DafnyTree method;

    ProofCenter pcenter;


    /**
     * Create all ProofVerificationConditions for a method
     * @param symbex_states
     * @param method
     */
    public ContractProofObligation(List<SymbexPath> symbex_states, DafnyTree method){
        pcenter  = ProofCenter.getInstance();
        this.method = method;
        createPVC(symbex_states);
    }

    /**
     * Create a proof verification condition using instantiated path conditions and
     * the instantiated proof obligation (represented as sibling no)
     * @param state
     * @param sibling_no
     * @return a new ProofVerificationConditionBuilder
     */
    private ProofVerificationConditionBuilder makeSinglePVC(SymbexPath state, int sibling_no){

        return new ProofVerificationConditionBuilder(state, sibling_no);
    }

    /**
     * This method iterates over all symbolic execution states and creates a ProofVerificationConditionBuilder for each
     * Condition and ProofObligation. The method adds each ProofVerificationConditionBuilder to the List of verification conditions
     * @param symbex_states
     */
    private void createPVC(List<SymbexPath> symbex_states) {

        verification_conditions = new LinkedList<ProofVerificationConditionBuilder>();

        //create a PVC for each PO of a Symbexstate
        for (SymbexPath symbex_state : symbex_states) {
            //get No of proof obligations in order to decide how many PVCs have to be created
            int no_of_po_siblings = symbex_state.getProofObligations().size();
            for (int i = 0; i < no_of_po_siblings; i++) {
                //make pvc and add into list of all PVCs
                verification_conditions.add(makeSinglePVC(symbex_state, i));
            }

        }



//has to be removed later on

        for (SymbexPath res : symbex_states) {


            System.out.println("------------");
            for (PathConditionElement pc : res.getPathConditions()) {
                System.out.println("Path condition - " + pc.getType());
                System.out.println("    " + pc.getExpression().toStringTree());
                System.out.println("  Assignment History:");
                System.out.println("    " + pc.getVariableMap().toHistoryString().replace("\n", "\n    "));
                System.out.println("  Aggregated Variable Map: ");
                System.out.println("    " + pc.getVariableMap().toParallelAssignment());
                System.out.println("  Instantiated condition: ");
                System.out.println("    " + pc.getVariableMap().instantiate(pc.getExpression()).toStringTree());
                System.out.println("  Refers to: line " + pc.getExpression().token.getLine());
                System.out.println("  Test Line: " + pc.getExpression());
            }

            System.out.println("Proof Obligations:");
            for (AssertionElement po : res.getProofObligations()) {
                System.out.println("  " + po);
            }

            System.out.println("  Assignment History:");
            System.out.println("    " + res.getMap().toHistoryString().replace("\n", "\n    "));
            System.out.println("  Aggregated Variable Map: ");
            System.out.println("    " + res.getMap().toParallelAssignment());
            System.out.println("  Instantiated POs: ");
            for (AssertionElement po : res.getProofObligations()) {
                System.out.println("    " + res.getMap().instantiate(po.getExpression()).toStringTree());
            }

        }}
}
