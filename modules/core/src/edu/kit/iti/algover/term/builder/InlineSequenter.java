/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
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
 *
 * @divedoc "VC generation/Inline"
 *
 * <h2>Sequent Generation with inlining all assignment</h2>
 *
 * <p><b>Name: <tt>inline</tt></b></p>
 *
 * <p>With this sequent generation all variable assignments are directly inlined
 * into the verification condition. This is what one would expect when applying
 * a vanilla weakest precondition calculus. No let expressions are produced at all.</p>
 *
 * <p>If you want to use this for verification condition, add to your input file:</p>
 * <p>
 *     settings {
 *         "Sequent Generation Type" = "inline"
 *     }
 * </p>
 *
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
