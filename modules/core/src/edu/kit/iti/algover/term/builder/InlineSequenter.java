/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;

public class InlineSequenter extends UpdateSequenter {

    private static final LetInlineVisitor LET_INLINE_VISITOR =
            new LetInlineVisitor();

    @Override
    public String getName() {
        return "inline";
    }

    @Override
    public String getDescriptiveName() {
        return "Inline all assignments";
    }

    @Override
    protected ProofFormula postProcess(ProofFormula formula) {
        Term term = formula.getTerm();
        try {
            term = term.accept(LET_INLINE_VISITOR, null);
        } catch (TermBuildException e) {
            // have an exception concept here!
            e.printStackTrace();
        }
        return new ProofFormula(formula.getID(), term, formula.getLabel());
    }

}