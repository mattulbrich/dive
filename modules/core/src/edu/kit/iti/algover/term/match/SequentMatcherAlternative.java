package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.ImmutableList;

public class SequentMatcherAlternative {
    private TermMatcher tm = new TermMatcher();

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

        for (ProofFormula formula : list) {
            ImmutableList<Matching> newMatches = tm.match(schema.getTerm(), formula.getTerm());
            // TODO Update polarity and formula number in the new matches
            if (!newMatches.isEmpty()) {
                ImmutableList<ProofFormula> remainder = list.filter(x -> x != formula);
                ImmutableList<Matching> newMatches2 = newMatches.flatMap(x -> matchSemiSequent(tail, remainder, polarity, x));
                result = result.appendAll(newMatches2);
            }
        }

        return result;
    }


}
