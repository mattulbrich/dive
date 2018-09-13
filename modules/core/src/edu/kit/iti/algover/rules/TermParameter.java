package edu.kit.iti.algover.rules;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.SchemaCaptureTerm;
import edu.kit.iti.algover.term.SchemaOccurTerm;
import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.MatchingEntry;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.term.match.TermMatcher;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;
import org.junit.Rule;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 9/5/18.
 */
public class TermParameter {
    //Inviariant: sequent != null && (term != null || schematicSequent != null || termSelector != null)

    private Term term;
    private TermSelector termSelector;
    private Sequent schematicSequent;
    private Sequent sequent;
    private Term schematicTerm;

    public TermParameter(Term term, Sequent sequent) {
        if(isTermSchematic(term)) {
            this.schematicTerm = term;
        } else {
            this.term = term;
        }
        this.sequent = sequent;
    }

    public TermParameter(TermSelector termSelector, Sequent sequent) {
        this.sequent = sequent;
        this.termSelector = termSelector;
    }

    public TermParameter(Sequent schematicSequent, Sequent sequent) {
        this.sequent = sequent;
        this.schematicSequent = schematicSequent;
    }

    public Term getTerm() throws RuleException {
        if(term != null) {
            return term;
        }
        if(termSelector != null) {
            term = termSelector.selectSubterm(sequent);
            return term;
        }
        SequentMatcher sequentMatcher = new SequentMatcher();
        ImmutableList<Matching> matchings = sequentMatcher.match(schematicSequent, sequent);
        if(matchings.size() == 0) {
            throw new RuleException("SchematicTerm " + schematicSequent + " does not match anything in sequent " + sequent);
        }
        if(matchings.size() > 1) {
            throw new RuleException("SchematicTerm " + schematicSequent + " matches more than one term in sequent " + sequent);
        }
        term = matchings.get(0).get("?match").getValue();
        return term;
    }

    public TermSelector getTermSelector() throws RuleException {
        if(termSelector != null) {
            return termSelector;
        }
        if(schematicSequent != null) {
            SequentMatcher sequentMatcher = new SequentMatcher();
            ImmutableList<Matching> matchings = sequentMatcher.match(schematicSequent, sequent);
            if (matchings.size() == 0) {
                throw new RuleException("SchematicTerm " + schematicSequent + " does not match anything in sequent " + sequent);
            }
            if (matchings.size() > 1) {
                throw new RuleException("SchematicTerm" + schematicSequent + " matches more than one term in sequent " + sequent);
            }
            MatchingEntry m = matchings.get(0).get("?match");
            if(m == null) {
                throw new RuleException("No ?match variable was found in schematic term " + schematicSequent);
            }
            m.getTermSelector();
            return termSelector;
        }

        if(schematicTerm != null) {
            if(containsMatchTerm(schematicTerm)) {
                termSelector = matchTermInSequentUniquely(schematicTerm, sequent);
            } else {
                SchemaCaptureTerm matchTerm = new SchemaCaptureTerm("?match", schematicTerm);
                termSelector = matchTermInSequentUniquely(matchTerm, sequent);
            }
            if(termSelector != null) {
                return termSelector;
            } else {
                throw new RuleException("SchematicTerm " + schematicTerm + " is not unique.");
            }
        }


        List<TermSelector> tss = RuleUtil.matchSubtermsInSequent(term::equals, sequent);
        if (tss.size() == 1) {
            termSelector = tss.get(0);
            return termSelector;
        }
        throw new RuleException("TermParameter: Could not find TermSelector for " + term + "in sequent " + sequent + ".");
    }

    public Sequent getSchematicTerm() throws RuleException {
        if(schematicSequent != null) {
            return schematicSequent;
        }

        if(schematicTerm != null) {
            if(containsMatchTerm(schematicTerm)) {
                termSelector = matchTermInSequentUniquely(schematicTerm, sequent);
            } else {
                SchemaCaptureTerm matchTerm = new SchemaCaptureTerm("?match", schematicTerm);
                termSelector = matchTermInSequentUniquely(matchTerm, sequent);
            }
            if(termSelector != null) {
                schematicSequent = getUniqueMatchingTerm(sequent, termSelector);
                return schematicSequent;
            } else {
                throw new RuleException("SchematicTerm " + schematicTerm + " is not unique.");
            }
        }

        if(termSelector != null) {
            return getUniqueMatchingTerm(sequent, termSelector);
        }

        return getUniqueMatchingTerm(sequent, term);
    }

    private Sequent getUniqueMatchingTerm(Sequent sequent, Term term)  throws RuleException {
        TermMatcher tm = new TermMatcher();
        Optional<TermSelector> ots = RuleUtil.matchSubtermInSequent(term::equals, sequent);
        if(ots.isPresent()) {
            return getUniqueMatchingTerm(sequent, ots.get(), term);
        }
        throw new RuleException();
    }

    private Sequent getUniqueMatchingTerm(Sequent sequent, TermSelector selector) throws RuleException {
        Term term = selector.selectSubterm(sequent);
        return getUniqueMatchingTerm(sequent, selector, term);
    }

    /**
     * Extracts a possibly schematic Term which is unique for the given TermSelector.
     *
     * @param sequent The sequent the TermSelector is related to.
     * @param selector The selector
     * @return a possibly schematic Term
     * @throws RuleException if no unique matching term is available (only if 2 identical Terms in same polarity)
     */
    private Sequent getUniqueMatchingTerm(Sequent sequent, TermSelector selector, Term t) throws RuleException {
        Term schemaCaptureTerm = new SchemaCaptureTerm("?match", t);
        t = new SchemaOccurTerm(schemaCaptureTerm);
        SequentMatcher sequentMatcher = new SequentMatcher();
        Sequent schemaSeq;
        if(selector.isSuccedent()) {
            schemaSeq = new Sequent(Collections.emptyList(), Collections.singletonList(new ProofFormula(t)));
        } else {
            schemaSeq = new Sequent(Collections.singletonList(new ProofFormula(t)), Collections.emptyList());
        }
        ImmutableList<Matching> matchings = sequentMatcher.match(schemaSeq, sequent);
        if(matchings.size() == 1) {
            return schemaSeq;
        }
        TermSelector parentSelector = getParentSelector(selector);

        if(parentSelector == null) {
            matchings.forEach(matching -> System.out.println("matching = " + matching));
            throw new RuleException("There is no unique matching term for a Parameter.");
        }
        return getUniqueMatchingTermRec(sequent, parentSelector,
                selector.getPath().get(selector.getPath().size() - 1), schemaCaptureTerm);
    }

    /**
     * Recursive version for {@link TermParameter#getUniqueMatchingTerm(Sequent, TermSelector)}.
     *
     * @param sequent
     * @param selector
     * @param childIdx
     * @param childTerm
     * @return
     * @throws RuleException
     */
    private Sequent getUniqueMatchingTermRec(Sequent sequent, TermSelector selector, int childIdx, Term childTerm) throws RuleException {
        Term t = selector.selectSubterm(sequent);
        Term schemaVarTerm = null;
        try {
            schemaVarTerm = ReplaceVisitor.replace(t, new SubtermSelector(childIdx), childTerm);
        } catch (TermBuildException e) {
            throw new RuleException("Error finding unique matching term.", e);
        }
        t = new SchemaOccurTerm(schemaVarTerm);
        SequentMatcher sequentMatcher = new SequentMatcher();
        Sequent schemaSeq;
        if(selector.isSuccedent()) {
            schemaSeq = new Sequent(Collections.emptyList(), Collections.singletonList(new ProofFormula(t)));
        } else {
            schemaSeq = new Sequent(Collections.singletonList(new ProofFormula(t)), Collections.emptyList());
        }
        ImmutableList<Matching> matchings = sequentMatcher.match(schemaSeq, sequent);
        if(matchings.size() == 1) {
            return schemaSeq;
        }
        TermSelector parentSelector = getParentSelector(selector);
        if(parentSelector == null) {
            throw new RuleException("There is no unique matching term for a Parameter.");
        }
        return getUniqueMatchingTermRec(sequent, parentSelector, selector.getPath().get(selector.getPath().size() - 1), schemaVarTerm);
    }

    /**
     * Gets a TermSelector which points to the parent term of the term selected by the given TermSelector
     *
     * @param selector the selector
     * @return the parent selector
     */
    private TermSelector getParentSelector(TermSelector selector) {
        if(selector.getPath().size() <= 0) {
            return null;
        }
        int intPath[] = new int[selector.getPath().size() - 1];
        for(int i = 0; i < intPath.length; ++i) {
            intPath[i] = selector.getPath().get(i);
        }

        return new TermSelector(selector.getPolarity(), selector.getTermNo(), intPath);
    }

    private boolean isTermSchematic(Term t) {
        Boolean b = t.accept(new IsSchematicVisitor(), null);
        return b.booleanValue();
    }

    private boolean containsMatchTerm(Term t) {
        Boolean b = t.accept(new ContainsMatchTermVisitor(), null);
        return b.booleanValue();
    }

    private class ContainsMatchTermVisitor extends DefaultTermVisitor<Object, Boolean, NoExceptions> {

        @Override
        protected Boolean defaultVisit(Term term, Object arg) throws NoExceptions {
            for (Term t : term.getSubterms()) {
                if( t.accept(this, arg)) {
                    return true;
                }
            }
            return Boolean.FALSE;
        }

        @Override
        public Boolean visit(SchemaCaptureTerm schemaCaptureTerm, Object arg) throws NoExceptions {
            if(schemaCaptureTerm.getName().equals("?match")) {
                return true;
            }
            for (Term t : term.getSubterms()) {
                if( t.accept(this, arg)) {
                    return true;
                }
            }
            return Boolean.FALSE;
        }

    }

    private class IsSchematicVisitor extends DefaultTermVisitor<Object, Boolean, NoExceptions> {

        @Override
        protected Boolean defaultVisit(Term term, Object arg) {
            for (Term t : term.getSubterms()) {
                if( t.accept(this, arg)) {
                    return true;
                }
            }
            return Boolean.FALSE;
        }

        @Override
        public Boolean visit(SchemaOccurTerm occurTerm, Object arg) {
            return Boolean.TRUE;
        }

        @Override
        public Boolean visit(SchemaCaptureTerm schemaCaptureTerm, Object arg) {
            return Boolean.TRUE;
        }

        @Override
        public Boolean visitSchemaTerm(SchemaTerm schemaTerm, Object arg) {
            return Boolean.TRUE;
        }

        @Override
        public Boolean visit(SchemaVarTerm schemaTerm, Object arg) {
            return Boolean.TRUE;
        }
    }

    private TermSelector matchTermInSequentUniquely(Term t, Sequent s) throws RuleException{
        TermMatcher tm = new TermMatcher();
        TermSelector ts = null;
        for(int i = 0; i < s.getAntecedent().size(); ++i) {
            ImmutableList<Matching> matches = tm.match(t, s.getAntecedent().get(i).getTerm());
            if(matches.size() == 1 && ts == null) {
                try {
                    ts = new TermSelector(new TermSelector("A." + i), matches.get(0).get("?match").getSelector());
                }  catch (FormatException e) {
                    e.printStackTrace();
                }
            } else if((matches.size() == 1 && ts != null) || matches.size() > 1) {
                throw new RuleException("Matching of term " + t + " in sequent " + s + "is ambiguous.");
            }
        }
        for(int i = 0; i < s.getSuccedent().size(); ++i) {
            ImmutableList<Matching> matches = tm.match(t, s.getSuccedent().get(i).getTerm());
            if(matches.size() == 1 && ts == null) {
                try {
                    ts = new TermSelector(new TermSelector("S." + i), matches.get(0).get("?match").getSelector());
                }  catch (FormatException e) {
                    e.printStackTrace();
                }
            } else if((matches.size() == 1 && ts != null) || matches.size() > 1) {
                throw new RuleException("Matching of term " + t + " in sequent " + s + "is ambiguous.");
            }
        }
        return ts;
    }
}
