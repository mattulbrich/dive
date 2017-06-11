/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.HashMap;
import java.util.Map;

import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.HistoryMap;
import edu.kit.iti.algover.util.Pair;

public class LetInlineVisitor extends
        ReplacementVisitor<HistoryMap<VariableTerm, Term>> {


    public static Term inline(Term term) throws TermBuildException {
        Term result = term.accept(new LetInlineVisitor(),
                new HistoryMap<>(new HashMap<>()));

        if (result == null) {
            result = term;
        }

        return result;
    }

    @Override
    public Term visit(VariableTerm variableTerm, HistoryMap<VariableTerm, Term> lets) throws TermBuildException {
        Term subst = lets.get(variableTerm);
        if(subst != null) {
            return subst;
        } else {
            return super.visit(variableTerm, lets);
        }
    }

    @Override
    public Term visit(LetTerm letTerm, HistoryMap<VariableTerm, Term> lets) throws TermBuildException {
        Map<VariableTerm, Term> newLets = new HashMap<>();
        for (Pair<VariableTerm, Term> ass : letTerm.getSubstitutions()) {
            VariableTerm f = ass.fst;
            Term replacement = ass.snd.accept(this, lets);
            if (replacement == null) {
                replacement = ass.snd;
            }
            newLets.put(f, replacement);
        }

        int rewindPos = lets.getHistory();
        lets.putAll(newLets);
        Term inner = letTerm.getTerm(0).accept(this, lets);
        lets.rewindHistory(rewindPos);

        if(inner == null) {
            return letTerm.getTerm(0);
        } else {
            return inner;
        }
    }
}
