package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

/**
 * Created by sarah on 11/2/15.
 */
public class AndRight implements ProofStep {


    /**
     * Eventuell ist Term nciht der richtige Parameter, evtl. muss noch die zugehörige Proof Formula übergeben werden wegen der Add und Delete List
     * @param t
     * @return
     */
    @Override
    public ProofStepResult apply(Term t) {
        if(canApply(t)){
//TODO

            return new ProofStepResult();
        }else {
            return null;
        }
    }

    /**
     * Checks whether AndRight Rule is applicable. This is
     * only the case when the term is an application term with top level symbol And
     * @param t
     * @return true iff AndRight is applicable, false otherwise
     */
    @Override
    public Boolean canApply(Term t) {
        if (t.getSort() == Sort.FORMULA){
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
            return null;
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
