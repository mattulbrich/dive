package edu.kit.iti.algover.util;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

import java.util.*;

public class ProofUtils {
    @TestInfrastructure
    public static ProofNodeSelector computeProofNodeSelector(String pathChild){
        String[] pathStringArray = pathChild.split(",");
        int[] path = Arrays.stream(pathStringArray).mapToInt(value -> Integer.parseInt(value)).toArray();
        ProofNodeSelector pns = new ProofNodeSelector(path);
        return pns;
    }


    @TestInfrastructure
    public static List<TermSelector> computeAllSelectors(Sequent lastSeq) throws FormatException {
        Set<TermSelector> selectors = new HashSet<>();
        List<ProofFormula> antecedent = lastSeq.getAntecedent();
        List<ProofFormula> succedent = lastSeq.getSuccedent();
        for (int i = 0; i < antecedent.size(); i++){
            ProofFormula form = antecedent.get(i);
            selectors.add(new TermSelector("A."+i));
            selectors.addAll(computeSelectorsWithCommonPrefix("A."+i, form.getTerm()));
        }
        for (int j = 0; j < succedent.size(); j++){
            ProofFormula form1 = succedent.get(j);
            selectors.add(new TermSelector("S."+j));
            selectors.addAll(computeSelectorsWithCommonPrefix("S."+j, form1.getTerm()));
        }
        return new ArrayList<>(selectors);
    }

    @TestInfrastructure
    public static Set<TermSelector> computeSelectorsWithCommonPrefix(String prefix, Term t) throws FormatException {
        Set<TermSelector> selectors = new HashSet<>();
        for(int i = 0; i<t.getSubterms().size(); i++) {
            selectors.add(new TermSelector(prefix+"."+i));
            selectors.addAll(computeSelectorsWithCommonPrefix(prefix+"."+i, t.getTerm(i)));
        }
        return selectors;
    }

}
