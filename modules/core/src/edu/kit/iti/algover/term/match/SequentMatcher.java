/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.ImmutableList;

public class SequentMatcher {
    private TermMatcher tm = new TermMatcher();

    /**
     * Matches a schematic seuqent against a concrete sequent
     *
     * @param schema
     * @param seq
     * @return a list of matchings
     */
    public ImmutableList<Matching> match(Sequent schema, Sequent seq) {

        ImmutableList<ProofFormula> schemaAnte = ImmutableList.from(schema.getAntecedent());
        ImmutableList<ProofFormula> schemaSucc = ImmutableList.from(schema.getSuccedent());

        ImmutableList<ProofFormula> ante = ImmutableList.from(seq.getAntecedent());
        ImmutableList<ProofFormula> succ = ImmutableList.from(seq.getSuccedent());

        Matching m = Matching.emptyMatching();

        ImmutableList<Matching> ms = matchSemiSequent(schemaAnte, ante, TermSelector.SequentPolarity.ANTECEDENT, m);

        ms = ms.flatMap(x -> matchSemiSequent(schemaSucc, succ, TermSelector.SequentPolarity.SUCCEDENT, x));

        return ms;
    }


    private ImmutableList<Matching> matchSemiSequent(ImmutableList<ProofFormula> schemaList, ImmutableList<ProofFormula> list, TermSelector.SequentPolarity polarity, Matching m) {

        if (schemaList.isEmpty())
            return ImmutableList.single(m);

        ProofFormula schema = schemaList.getLast();
        ImmutableList<ProofFormula> tail = schemaList.getTail();

        ImmutableList<Matching> result = ImmutableList.nil();

        int no = 0;

        for (ProofFormula formula : list) {
            ImmutableList<Matching> newMatches = tm.match(schema.getTerm(), formula.getTerm(), m);
            if (!newMatches.isEmpty()) {
                final int no2 = no;
                newMatches.forEach(x -> x.refineContext(polarity, no2));
                ImmutableList<ProofFormula> remainder = list.filter(x -> x != formula);
                ImmutableList<Matching> newMatches2 = newMatches.flatMap(x -> matchSemiSequent(tail, remainder, polarity, x));
                result = result.appendAll(newMatches2);
            }
            no++;
        }

        return result;
    }


}
