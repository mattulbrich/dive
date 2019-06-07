/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

public class ReferenceTools {

    public static void addSequentReferences(Sequent sequent,
            Map<Term, DafnyTree> termMap,
            Map<TermSelector, DafnyTree> target) {

        int i = 0;
        for (ProofFormula formula : sequent.getAntecedent()) {
            TermSelector sel = new TermSelector(SequentPolarity.ANTECEDENT, i);
            register(sel, formula.getTerm(), termMap, target);
            i++;
        }

        i = 0;
        for (ProofFormula formula : sequent.getSuccedent()) {
            TermSelector sel = new TermSelector(SequentPolarity.SUCCEDENT, i);
            register(sel, formula.getTerm(), termMap, target);
            i++;
        }

    }

    private static void register(TermSelector sel, Term term,
            Map<Term, DafnyTree> termMap,
            Map<TermSelector, DafnyTree> target) {

        DafnyTree mapped = termMap.get(term);
        if(mapped == null) {
            // System.err.println(sel + " is not mapped: " + term);
        } else {
            target.put(sel, mapped);
        }

        List<Term> subterms = term.getSubterms();
        int i = 0;
        for (Term t : subterms) {
            register(sel.selectSubterm(i), t, termMap, target);
            i++;
        }

    }

}
