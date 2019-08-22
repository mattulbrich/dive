/*
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.term;

import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;

public class ReferenceTerm extends SchemaTerm {

    private final TermSelector selector;

    public ReferenceTerm(TermSelector selector, Term term) {
        super(term.getSort(), new Term[] { term });
        this.selector = selector;
    }

    // MOVE THESE TWO TO RULEUTIL OR SIMILAR CLASS IN THE RULE INFRASTRUCTURE
    public static Term select(TermParameter term, int... sub) throws RuleException {
        return select(term, new SubtermSelector(sub));
    }

    public static Term select(TermParameter term, SubtermSelector selector) throws RuleException {
        Term subterm = selector.selectSubterm(term.getTerm());
        return new ReferenceTerm(new TermSelector(term.getTermSelector(), selector), subterm);
    }

    @Override
    public String toString() {
        // not to be parsed, hence, representation does not really matter
        return "[" + selector + "](" + getTerm(0).toString() + ")";
    }

    @Override
    public <A, R, E extends Exception> R accept(TermVisitor<A, R, E> visitor, A arg) throws E {
        return visitor.visit(this, arg);
    }

    @Override
    public SchemaTerm refineSort(Sort newSort) {
        // TODO not finished
        return null;
    }
}
