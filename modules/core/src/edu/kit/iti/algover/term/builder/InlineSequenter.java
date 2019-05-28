/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

import java.util.Map;

/**
 * This sequenter takes is a specialisation of an update sequenter.
 *
 * It removes the let-cascade by inlining the updates.
 *
 * @author Mattias Ulbrich
 */
public class InlineSequenter extends UpdateSequenter {

    @Override
    public String getName() {
        return "inline";
    }

    @Override
    public String getDescriptiveName() {
        return "Inline all assignments";
    }

    @Override
    protected ProofFormula postProcess(ProofFormula formula, Map<Term, DafnyTree> referenceMap) {
        Term term = formula.getTerm();
        try {
            term = LetInlineVisitor.inline(referenceMap, term);
        } catch (TermBuildException e) {
            // have an exception concept here!
            e.printStackTrace();
        }
        return new ProofFormula(term, formula.getLabels());
    }

}
