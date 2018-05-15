package edu.kit.iti.algover.term.match;

import com.google.common.collect.Sets;
import com.sun.org.apache.xerces.internal.impl.xpath.regex.Match;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.SchemaOccurTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Triple;

import java.util.*;

public class SequentMatcher {

    /**
     * Match a schematic Sequent against another Sequent.
     *
     * <p> The result may be 0, 1 or more {@link Matching}s. This is since the
     * ellipsis operator may match differently at different points. </p>
     *
     * <p> The second sequent will in most cases be a sequqnt w/o schematic entities.
     * This is not strictly required, however. But matching happens only in the
     * first argument. Hence, {@code ?x} matches against {@code 42}, but not
     * {@code 42} does not match against {@code ?x}. </p>
     *
     * @param schematicSeq the sequent with the schema entities
     * @param concreteSeq  the sequent to match against
     * @return a list of all matchings which unify the two arguments.
     */
    public ImmutableList<Matching> match(Sequent schematicSeq, Sequent concreteSeq) {
        return match(schematicSeq, concreteSeq, Matching.emptyMatching());
    }

    /**
     * Match a schematic term against another term.
     *
     * <p> The result may be 0, 1 or more {@link Matching}s. This is since the
     * ellipsis operator may match differently at different points. </p>
     *
     * <p> The second term will in most cases be a term w/o schematic entities.
     * This is not strictly required, however. But matching happens only in the
     * first argument. Hence, {@code ?x} matches against {@code 42}, but not
     * {@code 42} does not match against {@code ?x}. </p>
     *
     * <p>This method does not start with an empty matching context but with the
     * one specified in m.</p>
     *
     * @param schem the term with the schema entities
     * @param conc  the term to match against
     * @param m     the matching to begin from.
     * @return a list of all matchings which unify the two arguments.
     */
    private ImmutableList<Matching> match(Sequent schem, Sequent conc, Matching m) {
        List<ProofFormula> antecedent = schem.getAntecedent();
        List<ProofFormula> succedent = schem.getSuccedent();

        ImmutableList<Matching> antecMatchings;
        ImmutableList<Matching> succMatchings;

        succMatchings = match(succedent, conc.getSuccedent(), m);
        antecMatchings = match(antecedent, conc.getAntecedent(), m);
        //matchings have to be conformly reduced s.t. variable assignaments on both sides are not contradictory

        return reduceConform(succMatchings, antecMatchings);


    }


    /**
     * Match a semisequent pattern against a concrete semisequent
     *
     * @param schemCedent
     * @param concCedent
     * @param m
     * @return
     */
    private ImmutableList<Matching> match(List<ProofFormula> schemCedent, List<ProofFormula> concCedent, Matching m) {
        //shortcuts if pattern is empty, the sequent is matched in any case
        if (concCedent.isEmpty()) {
            if (schemCedent.isEmpty()) {
                //matching but without variable assignments
                return ImmutableList.single(Matching.emptyMatching());
            } else {
                //no match
                return ImmutableList.nil();
            }
        }

        // if we have an empty pattern, then it is always a match
        if (!concCedent.isEmpty() && schemCedent.isEmpty()) {
            return ImmutableList.single(Matching.emptyMatching());
        }
        TermMatcher tm = new TermMatcher();

        Map<ProofFormula, Map<ProofFormula, ImmutableList<Matching>>> mapOfMatches = new LinkedHashMap<>();
        for (ProofFormula patternTerm : schemCedent) {
            mapOfMatches.put(patternTerm, new HashMap<>());
            for (ProofFormula concreteFormula : concCedent) {
                ImmutableList<Matching> temp = tm.match(patternTerm.getTerm(), concreteFormula.getTerm());
                if (!temp.isEmpty()) {
                    mapOfMatches.get(patternTerm).put(concreteFormula, temp);
                }
            }
        }

        List<Matching> matchings = new ArrayList<>();
        reduceDisjoint(mapOfMatches, schemCedent, matchings);
        if (mapOfMatches.values().stream().allMatch(Map::isEmpty))
            //if no match has been found the sequent does not match return nil
            return ImmutableList.nil();

        ImmutableList<Matching> ret = ImmutableList.from(matchings);
        return ret;
    }

    /**
     * Reduce all found matchings by checking their compatibility and combining the matchings
     *
     * @param mapOfMatches
     * @param patternFormulas
     * @param matchings
     */
    private void reduceDisjoint(Map<ProofFormula, Map<ProofFormula, ImmutableList<Matching>>> mapOfMatches,
                                List<ProofFormula> patternFormulas, List<Matching> matchings) {
        reduceDisjoint(mapOfMatches, patternFormulas, matchings, 0, Matching.emptyMatching(), new HashSet<>());

    }

    /**
     * Reduce all matchings.
     * If same variable names are referencing different term values in matchings of both semisequents,
     * matching has to be reduced to "No match". Otherwise matchings should be merged and duplicates should be removed
     *
     * @param succMatchings
     * @param antecMatchings
     * @return
     */
    private ImmutableList<Matching> reduceConform(ImmutableList<Matching> succMatchings, ImmutableList<Matching> antecMatchings) {
        //if one side did not match at all
        if (succMatchings.isEmpty() || antecMatchings.isEmpty()) {
            return ImmutableList.nil();
        }
        if (succMatchings.size() == 1 && antecMatchings.size() == 1) {
            Matching matching = reduceConform(succMatchings.get(0), antecMatchings.get(0));
            if (matching != null) {
                return ImmutableList.single(matching);
            } else {
                return ImmutableList.nil();
            }
        } else {
            //build product
            List<Matching> returnedMatchings = new ArrayList<>();
            antecMatchings.forEach(matching -> {
                succMatchings.forEach(matching1 -> {
                    Matching m = reduceConform(matching1, matching);
                    if (m != null) {
                        returnedMatchings.add(m);

                    }
                });
            });
            return ImmutableList.from(returnedMatchings);

        }

    }

    private void reduceDisjoint(Map<ProofFormula, Map<ProofFormula, ImmutableList<Matching>>> mapOfMatches,
                                List<ProofFormula> patternFormulas,
                                List<Matching> matchings, int position,
                                Matching returnMatching,
                                Set<ProofFormula> chosenProofFormula) {

        if (position >= patternFormulas.size()) {
            matchings.add(returnMatching);
            return;
        }

        ProofFormula currentPatternForm = patternFormulas.get(position);
        Sets.SetView<ProofFormula> topLevelFormulas =
                Sets.difference(mapOfMatches.get(currentPatternForm).keySet(), chosenProofFormula);

        if (topLevelFormulas.size() == 0) {
            return;
        }

        for (ProofFormula formula : topLevelFormulas) {
            ImmutableList<Matching> m = mapOfMatches.get(currentPatternForm).get(formula);
            if (m.size() == 1) {
                Matching matching = m.get(0);
                Matching temp = reduceConform(matching, returnMatching);
                if (temp != null) {
                    chosenProofFormula.add(formula);
                    reduceDisjoint(mapOfMatches, patternFormulas, matchings, position + 1, temp, chosenProofFormula);
                }
            }

        }

    }

    private Matching reduceConform(Matching newM, Matching alreadyExistingMatching) {
        if (newM.equals(Matching.emptyMatching())) return alreadyExistingMatching;
        if (alreadyExistingMatching.equals(Matching.emptyMatching())) return newM;


        //ok we have matching entries in both matchings, now we have to
        //reduce them to an entry that is conform
        ImmutableList<MatchingEntry> entriesOfNew = newM.getEntries();
        ImmutableList<MatchingEntry> entriesOfExisting = alreadyExistingMatching.getEntries();

        //get all keys to compare
        ImmutableList<String> keyListExisting = entriesOfExisting.map(matchingEntry -> matchingEntry.getKey());
        ImmutableList<String> keyListNew = entriesOfNew.map(matchingEntry -> matchingEntry.getKey());


        //filter out if variable assignments are not referencing the same termvalue
        //TODO: This is the place where joining of matchingentries has to take place if more than one subtermselector is needed
        for (String s : keyListNew) {

            if (keyListExisting.contains(s)) {
                Term newEntry = newM.get(s).getValue();
                Term existingEntry = alreadyExistingMatching.get(s).getValue();
                if (!existingEntry.equals(newEntry)) {
                    if (!s.startsWith("_")) {
                        System.out.println("Entries are not conform");
                        return null;
                    } else {
                        System.out.println("We arrived at a don't care, picking the first entry of existing");
                    }
                }

            } else {
                //add entry as it was not in matching before
                MatchingEntry newEntry = entriesOfNew.findFirst(matchingEntry -> matchingEntry.getKey().equals(s));
                alreadyExistingMatching.add(newEntry.getKey(), newEntry.getValue(), newEntry.getSelector());
            }

        }
        return alreadyExistingMatching;

    }
}


