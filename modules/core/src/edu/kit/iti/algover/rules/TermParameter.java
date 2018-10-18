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
import nonnull.NonNull;
import org.junit.Rule;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 9/5/18.
 *
 * This class is used to create a Parameter type for terms in rule applications.
 * The purpose is to wrap different representations of the same parameter. To be able
 * to translate between different representations this parameters have to be based on a
 * concrete sequent.
 * A TermParameter may contain 4 different representations:
 * - TermSelector
 * - concrete Term
 * - schematic Sequent
 * - schematic Term
 * By now conversions between the first 3 are fully supported (if possible). Schematic Terms are only accessible
 * if given on instantiation (this may be extended if needed). Not all conversions are theoretically possible
 * since a concrete Term may occur several times in one sequent and thus not be convertible to a TermSelector.
 *
 * If the requested representation is not yet calculated the least calculation intensive conversion
 * should be used (may this needs some improvements here).
 * Meaning:
 * Term: termSelector > schematicSequent > schematicTerm
 * termSelector: term > schematicSequent > schematicTerm
 * schematicSequent: schematicTerm > termSelector > term
 *
 */
public class TermParameter {
    //Inviariant: sequent != null && (term != null || schematicSequent != null || termSelector != null)

    private Term term;
    private Term oterm;
    private TermSelector termSelector;
    private TermSelector oTermSelector;
    private Sequent schematicSequent;
    private Sequent oSchematicSequent;
    private Sequent sequent;
    private Term schematicTerm;
    private Term originalSchematicTerm;

    public TermParameter(@NonNull Term term, @NonNull Sequent sequent) {
        if(isTermSchematic(term)) {
            this.schematicTerm = term;
            this.originalSchematicTerm = term;
        } else {
            this.term = term;
            this.oterm = term;
        }
        this.sequent = sequent;
    }

    public TermParameter(@NonNull TermSelector termSelector, @NonNull Sequent sequent) {
        this.sequent = sequent;
        this.termSelector = termSelector;
        this.oTermSelector = termSelector;
    }

    public TermParameter(@NonNull Sequent schematicSequent, @NonNull Sequent sequent) {
        this.sequent = sequent;
        this.schematicSequent = schematicSequent;
        this.oSchematicSequent = schematicSequent;
    }

    /**
     * Returns a concrete Term (no schematic elements) representing this TermParameter.
     * If not already present this term is translated from one of the present representations.
     *
     * @return the concrete Term
     * @throws RuleException
     */
    public Term getTerm() throws RuleException {
        if(term != null) {
            return term;
        }
        if(termSelector != null) {
            term = termSelector.selectSubterm(sequent);
            return term;
        }

        if(schematicSequent != null) {
            MatchingEntry m = getUniqueMatchingInSequent(schematicSequent, sequent);
            term = m.getValue();
            return term;
        }

        term = matchTermInSequentUniquelyT(schematicTerm, sequent);
        return term;
    }

    /**
     * returns the Term that was given on initialisation or null
     *
     * @return term as on initialisation
     */
    public Term getOriginalTerm() {
        return oterm;
    }

    /**
     * Returns a TermSelector representing this TermParameter.
     * If not already present this termSelector is translated from one of the present representations.
     *
     * @return the termSelector
     * @throws RuleException
     */
    public TermSelector getTermSelector() throws RuleException {
        if(termSelector != null) {
            return termSelector;
        }

        if(term != null) {
            List<TermSelector> tss = RuleUtil.matchSubtermsInSequent(term::equals, sequent);
            if (tss.size() == 1) {
                termSelector = tss.get(0);
                return termSelector;
            }
        }

        if(schematicSequent != null) {
            MatchingEntry m = getUniqueMatchingInSequent(schematicSequent, sequent);
            termSelector = m.getTermSelector();
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

        throw new RuleException("TermParameter with all components are null.");
    }

    private MatchingEntry getUniqueMatchingInSequent(Sequent t, Sequent s) throws RuleException {
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
        return m;
    }

    /**
     * Returns a schematic Term representing this TermParameter.
     * NOTE: This is only supported if the TermParameter was initlialized with a schematic Term.
     * No translation from other representations is supported.
     *
     * @return the schematic Term
     * @throws RuleException
     */
    public Term getSchematicTerm() throws RuleException {
        if(schematicTerm != null) {
            return schematicTerm;
        }
        throw new RuleException("No schematic term was given for this parameter.");
    }

    /**
     * Returns a schematicSequent representing this TermParameter.
     * If not already present this sequent is translated from one of the present representations.
     *
     * @return the schematic sequent
     * @throws RuleException
     */
    public Sequent getSchematicSequent() throws RuleException {
        if(schematicSequent != null) {
            return schematicSequent;
        }

        if(schematicTerm != null) {
            Term st = new SchemaOccurTerm(schematicTerm);
            Sequent s = new Sequent(new ArrayList<>(), Collections.singletonList(new ProofFormula(st)));
            SequentMatcher sequentMatcher = new SequentMatcher();
            ImmutableList<Matching> matchings = sequentMatcher.match(s, sequent);
            if (matchings.size() == 1) {
                schematicSequent = s;
                return schematicSequent;
            } else {
                s = new Sequent(Collections.singletonList(new ProofFormula(st)), new ArrayList<>());
                matchings = sequentMatcher.match(s, sequent);
                if (matchings.size() == 0) {
                    throw new RuleException("SchematicTerm " + s + " does not match anything in sequent " + sequent);
                }
                if (matchings.size() > 1) {
                    throw new RuleException("SchematicTerm" + s + " matches more than one term in sequent " + sequent);
                }
                schematicSequent = s;
                return s;
            }
        }

        if(termSelector != null) {
            schematicSequent = getUniqueMatchingTerm(sequent, termSelector);
            return schematicSequent;
        }

        schematicSequent = getUniqueMatchingTerm(sequent, term);
        return schematicSequent;
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
     * Extracts a schematic sequent which is unique for the given TermSelector.
     *
     * @param sequent The sequent the TermSelector is related to.
     * @param selector The selector
     * @return a schematic sequent
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
            throw new RuleException("There is no unique matching sequent for TermParameter: " + this);
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

    public TermSelector getOrigianlTermSelector() {
        return oTermSelector;
    }

    public Sequent getOriginalSchematicSequent() {
        return oSchematicSequent;
    }

    public Term getOriginalSchematicTerm() {
        return originalSchematicTerm;
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

    private Term matchTermInSequentUniquelyT(Term t, Sequent s) throws RuleException{
        TermMatcher tm = new TermMatcher();
        Term ts = null;
        for(int i = 0; i < s.getAntecedent().size(); ++i) {
            ImmutableList<Matching> matches = tm.match(t, s.getAntecedent().get(i).getTerm());
            if(matches.size() == 1 && ts == null) {
                try {
                    ts = matches.get(0).get("?match").getValue();
                } catch (NullPointerException e) {
                    throw new RuleException("Schematic Term has to contain ?match variable.");
                }
            } else if((matches.size() == 1 && ts != null) || matches.size() > 1) {
                throw new RuleException("Matching of term " + t + " in sequent " + s + "is ambiguous.");
            }
        }
        for(int i = 0; i < s.getSuccedent().size(); ++i) {
            ImmutableList<Matching> matches = tm.match(t, s.getSuccedent().get(i).getTerm());
            if(matches.size() == 1 && ts == null) {
                try {
                    ts = matches.get(0).get("?match").getValue();
                } catch (NullPointerException e) {
                    throw new RuleException("Schematic Term has to contain ?match variable.");
                }
            } else if((matches.size() == 1 && ts != null) || matches.size() > 1) {
                throw new RuleException("Matching of term " + t + " in sequent " + s + "is ambiguous.");
            }
        }
        return ts;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("TermParameter[");
        sb.append("term = " + term);
        sb.append(", schematicTerm = " + schematicTerm);
        sb.append(", schematicSequent = " + schematicSequent);
        sb.append(", TermSelector = " + termSelector);
        sb.append("]");
        return sb.toString();
    }
}
