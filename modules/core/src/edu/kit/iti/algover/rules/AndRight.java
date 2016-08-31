/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;

import java.util.List;

/**
 * Created by sarah on 11/2/15.
 */
public class AndRight implements ProofStep {


    /**
     * Eventuell ist Term nicht der richtige Parameter, evtl. muss noch die zugehörige Proof Formula übergeben werden wegen der Add und Delete List
     * @param t
     * @return
     */
    @Override
    public ProofStepResult apply(ProofFormula form, Term t, List<ProofFormula> side_conditions) {
        if(possibleApplications(form, t, side_conditions)){
            ImmutableList<ProofFormula> addList = ImmutableList.nil();
            ImmutableList<ProofFormula> delList = ImmutableList.nil();
            delList.append(form);
            ApplTerm term = (ApplTerm) t;
            List<Term> subterms = term.getSubterms();
            for (Term subterm : subterms) {
                //new proofFormula, we need latest index
                //then add into addlist
            }
//create new proofstepresult with both lists
            return new ProofStepResult();
        }else {
            return null;
        }
    }

    /**
     * Checks whether AndRight Rule is applicable. This is
     * only the case when the term is an application term with top level symbol
     * ---And VGL auf Formula
     * Needs to be rewritten
     * @param t
     * @return true iff AndRight is applicable, false otherwise
     */
    @Override
    public boolean possibleApplications(ProofFormula form, Term t, List<ProofFormula> side_conditions) {
        Term toplevel = form.getTerm();
        if (toplevel.getSort() == Sort.FORMULA){
         if(t instanceof ApplTerm){
             ApplTerm term = (ApplTerm) t;
             if(term.getFunctionSymbol().equals(BuiltinSymbols.AND)){
                 return true;
             }else{
                 return false;
             }
         }else{
             return false;
         }
        }else {
            return false;
        }
    }

    @Override
    public String getRuleName() {
        return null;
    }

    @Override
    public String getCategory() {
        return null;
    }
}