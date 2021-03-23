/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;

import java.util.ArrayList;
import java.util.List;

public class SequentMatcher {
    private TermMatcher tm = new TermMatcher();

    /**
     * Matches a schematic sequent against a concrete sequent
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

    public List<ImmutableList<Matching>> matchTermInSequent(Sequent sequent, Term term) {
        List<ImmutableList<Matching>> matchings = matchTermInSemiSequent(sequent, term, TermSelector.SequentPolarity.ANTECEDENT);
        matchings.addAll(matchTermInSemiSequent(sequent, term, TermSelector.SequentPolarity.SUCCEDENT));

        return matchings;
    }

    public List<ImmutableList<Matching>> matchTermInSemiSequent(Sequent sequent, Term term, TermSelector.SequentPolarity polarity) {

        List<ImmutableList<Matching>> result = new ArrayList<>();
        ImmutableList<ProofFormula> list = ImmutableList.from(polarity == TermSelector.SequentPolarity.ANTECEDENT ? sequent.getAntecedent() : sequent.getSuccedent());

        for (ProofFormula formula : list) {
            result.addAll(matchTermInTermRec(formula.getTerm(), term));
        }

        return result;
    }

    public List<ImmutableList<Matching>> matchTermInTermRec(Term term, Term matchTerm) {
        List<ImmutableList<Matching>> res = new ArrayList<>();
        for(Term t : term.getSubterms()) {
            res.addAll(matchTermInTermRec(t, matchTerm));
        }
        ImmutableList<Matching> newMatches = tm.match(matchTerm, term);
        if(!newMatches.isEmpty()) {
            res.add(newMatches);
        }
        return res;
    }


}
