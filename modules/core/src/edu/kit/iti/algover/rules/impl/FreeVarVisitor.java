/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Stack;

/**
 * Collect the variables that occur free (i.e. not in the scope of a quantifier
 * or let-binder) in a term or terms.
 *
 * The result is a {@link Set} object.
 *
 * @author mulbrich
 * @see SubstitutionVisitor
 *
 */
public class FreeVarVisitor extends DefaultTermVisitor<Void, Void, NoExceptions> {

    private Set<VariableTerm> freeVars = new HashSet<>();
    private ImmutableList<VariableTerm> boundVars = ImmutableList.nil();

    @Override
    protected Void defaultVisit(Term term, Void arg) {
        for (Term t : term.getSubterms()) {
            t.accept(this, null);
        }
        return null;
    }

    @Override
    public Void visit(LetTerm term, Void arg) throws NoExceptions {
        ImmutableList<VariableTerm> oldBounds = boundVars;
        term.getTerm(0).accept(this, null);

        boundVars = boundVars.appendAll(
                ImmutableList.from(term.getSubstitutions()).map(Pair::getFst));
        for (int i = 1; i < term.countTerms(); i++) {
            term.getTerm(i).accept(this, null);
        }

        boundVars = oldBounds;
        return null;
    }

    @Override
    public Void visit(QuantTerm term, Void arg) throws NoExceptions {
        boundVars = boundVars.append(term.getBoundVar());
        super.visit(term, arg);
        boundVars = boundVars.getTail();
        return null;
    }

    @Override
    public Void visit(VariableTerm term, Void arg) throws NoExceptions {
        if (!boundVars.contains(term)) {
            freeVars.add(term);
        }
        return null;
    }

    public static Set<VariableTerm> findFreeVars(Iterable<Term> terms) {
        FreeVarVisitor visitor = new FreeVarVisitor();
        terms.forEach(x->x.accept(visitor, null));
        return visitor.freeVars;
    }

    public static Set<VariableTerm> findFreeVars(Term term) {
        FreeVarVisitor visitor = new FreeVarVisitor();
        term.accept(visitor, null);
        return visitor.freeVars;
    }
}
