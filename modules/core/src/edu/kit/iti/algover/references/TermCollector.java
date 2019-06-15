/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.*;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Philipp on 27.08.2017.
 */
public class TermCollector implements TermVisitor<TermSelector,Void,NoExceptions> {

    public void collectInSequent(Sequent sequent, TermSelector selector) throws RuleException {
        selector.selectSubterm(sequent).accept(this, selector);
    }

    private final Map<TermSelector, Term> collectedTerms;

    public TermCollector() {
        collectedTerms = new HashMap<>();
    }

    public Map<TermSelector, Term> getCollectedTerms() {
        return collectedTerms;
    }

    private Void visitTerm(Term term, TermSelector selector) {
        collectedTerms.put(selector, term);

        for (int i = 0; i < term.countTerms(); i++) {
            TermSelector subSelector = new TermSelector(selector, i);
            term.getSubterms().get(i).accept(this, subSelector);
        }
        return null;
    }

    @Override
    public Void visit(VariableTerm variableTerm, TermSelector selector) throws NoExceptions {
        return visitTerm(variableTerm, selector);
    }

    @Override
    public Void visit(SchemaVarTerm schemaVarTerm, TermSelector selector) throws NoExceptions {
        return visitTerm(schemaVarTerm, selector);
    }

    @Override
    public Void visit(QuantTerm quantTerm, TermSelector selector) throws NoExceptions {
        return visitTerm(quantTerm, selector);
    }

    @Override
    public Void visit(ApplTerm applTerm, TermSelector selector) throws NoExceptions {
        return visitTerm(applTerm, selector);
    }

    @Override
    public Void visit(LetTerm letTerm, TermSelector selector) throws NoExceptions {
        return visitTerm(letTerm, selector);
    }
}
