package edu.kit.iti.algover.util;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class ProofMockUtil {

    public static Term TRUE;
    public static Term FALSE;

    static {
        try {
            TRUE = new ApplTerm(BuiltinSymbols.TRUE);
            FALSE = new ApplTerm(BuiltinSymbols.FALSE);
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
    }

    public static ProofNode mockProofNode(ProofNode parent, Term[] antedecentTerms, Term[] succedentTerms) throws TermBuildException {
        List<ProofFormula> antedecentFormulas = new ArrayList<>(antedecentTerms.length);
        for (int i = 0; i < antedecentTerms.length; i++) {
            antedecentFormulas.add(new ProofFormula(i, antedecentTerms[i]));
        }
        List<ProofFormula> succedentFormulas = new ArrayList<>(succedentTerms.length);
        for (int i = 0; i < succedentTerms.length; i++) {
            succedentFormulas.add(new ProofFormula(i, succedentTerms[i]));
        }
        return new ProofNode(parent, null, null,
                new Sequent(antedecentFormulas, succedentFormulas), null);
    }
}
