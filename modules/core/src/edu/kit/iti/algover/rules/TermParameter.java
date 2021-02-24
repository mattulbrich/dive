/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.MatchingEntry;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.term.match.TermMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.*;

/**
 * This class is used to create a Parameter type for terms in rule applications.
 * The purpose is to wrap different representations of the same term reference
 * within a sequent. To be able to translate between different representations
 * this parameters have to be based on a concrete sequent.
 * <p>
 * A TermParameter may contain 4 different representations:
 * <ul>
 * <li> a {@link TermSelector}
 * <li> a concrete {@link Term}
 * <li> a schematic {@link Sequent}
 * <li> a schematic {@link Term}
 * </ul>
 * By now conversions between the first 3 are fully supported (if possible).
 * Schematic terms are only accessible if given on instantiation (this may be
 * extended if needed). Not all conversions are theoretically possible since a
 * concrete Term may occur several times in one sequent and thus not be
 * convertible to a TermSelector. {@link RuleException}s are thrown if
 * conversions fails.
 *
 * If the requested representation is not yet calculated, the least calculation
 * intensive conversion should be used (maybe this needs some improvements
 * here), meaning:
 * <pre>
 * Term: termSelector > schematicSequent > schematicTerm
 * termSelector: term > schematicSequent > schematicTerm
 * schematicSequent: schematicTerm > termSelector > term
 * </pre>
 *
 * @author Jonas Klamroth, 9/5/18.
 * @see ParameterType
 */
public class TermParameter {
    // Invariant: sequent != null &&
    //   (term != null || schematicSequent != null || termSelector != null)
    //   && exactly-one-is-not-null(oterm, oSchematicSequent, oSchematicTerm)

    private Sequent sequent;

    private Term term;
    private Term oterm;
    private TermSelector termSelector;
    private TermSelector oTermSelector;
    private Sequent schematicSequent;
    private Sequent oSchematicSequent;
    private Term schematicTerm;
    private Term oSchematicTerm;
    private static final String matchKeyword = "?m";

    /**
     * Create a term parameter from a <em>schematic</em> or <em>concrete</em>
     * term and a concrete sequent.
     *
     * @param term    a schematic or concrete term describing the parameter
     * @param sequent the concrete sequent within which the schematic term is to
     *                be located
     */
    public TermParameter(@NonNull Term term, @NonNull Sequent sequent) {
        this.sequent = sequent;
        if (isTermSchematic(term)) {
            this.schematicTerm = term;
            this.oSchematicTerm = term;
        } else {
            this.term = term;
            this.oterm = term;
        }
    }


    private Term getMostInnerTerm(Term term) {
        if(term.getSubterms().size() >= 1 && !(term instanceof ApplTerm)) {
            return getMostInnerTerm(term.getTerm(0));
        }
        return term;
    }

    /**
     * Create a term parameter from a <em>schematic</em> or <em>concrete</em>
     * term and a concrete sequent.
     *
     * @param termSelector a term selector describing the parameter
     * @param sequent      the concrete sequent within which the term selector
     *                     applies
     */
    public TermParameter(@NonNull TermSelector termSelector, @NonNull Sequent sequent) {
        this.sequent = sequent;
        this.termSelector = termSelector;
        this.oTermSelector = termSelector;
    }

    /**
     * Create a term parameter from a <em>schematic</em> (partial) sequent and a
     * concrete sequent.
     *
     * @param schematicSequent a partial sequent describing the parameter
     * @param sequent          the concrete sequent within which the term
     *                         selector applies
     */
    public TermParameter(@NonNull Sequent schematicSequent, @NonNull Sequent sequent) {
        this.sequent = sequent;
        this.schematicSequent = schematicSequent;
        this.oSchematicSequent = schematicSequent;
    }

    /**
     * Returns a concrete {@link Term} (no schematic elements) representing this
     * TermParameter. If not already present, this term is translated from one
     * of the present representations.
     *
     * @return the concrete {@link Term} representing this parameter
     * @throws RuleException if matching is not feasible or not unique
     */
    public @NonNull Term getTerm() throws RuleException {
        if(term != null) {
            return term;
        }

        if(oTermSelector != null) {
            term = oTermSelector.selectSubterm(sequent);
            return term;
        }

        if(oSchematicSequent != null) {
            MatchingEntry m = getUniqueMatchingInSequent(oSchematicSequent, sequent);
            term = m.getValue();
            return term;
        }

        assert oSchematicTerm != null;
        if(containsMatchTerm(oSchematicTerm)) {
            termSelector = matchTermInSequentUniquely(oSchematicTerm, sequent);
        } else {
            SchemaCaptureTerm matchTerm = new SchemaCaptureTerm(matchKeyword, oSchematicTerm);
            termSelector = matchTermInSequentUniquely(matchTerm, sequent);
        }
        term = termSelector.selectSubterm(sequent);
        return term;
    }



    /**
     * Returns a TermSelector representing this TermParameter.
     * If not already present, this termSelector is translated from one of the present representations.
     *
     * @return the termSelector representing this parameter
     * @throws RuleException if matching is not feasible or not unique
     */
    public @NonNull TermSelector getTermSelector() throws RuleException {
        if(termSelector != null) {
            return termSelector;
        }

        if(oterm != null) {
            List<TermSelector> tss = RuleUtil.matchSubtermsInSequent(oterm::equals, sequent);
            if (tss.size() != 1) {
                throw new RuleException("Term " + oterm + " is not unique.");
            }
            termSelector = tss.get(0);
            return termSelector;
        }

        if(oSchematicSequent != null) {
            MatchingEntry m = getUniqueMatchingInSequent(oSchematicSequent, sequent);
            termSelector = m.getTermSelector();
            return termSelector;
        }

        if(oSchematicTerm != null) {
            if(containsMatchTerm(oSchematicTerm)) {
                termSelector = matchTermInSequentUniquely(oSchematicTerm, sequent);
            } else {
                SchemaCaptureTerm matchTerm = new SchemaCaptureTerm("?match", oSchematicTerm);
                termSelector = matchTermInSequentUniquely(matchTerm, sequent);
            }

            if(termSelector != null) {
                return termSelector;
            } else {
                throw new RuleException("SchematicTerm " + schematicTerm + " is not unique.");
            }
        }

        // That is an internal error that should not occur.
        throw new RuleException("TermParameter with all components null.");
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
     * Creates a list of possible matching terms based an this TermParameters term and termSelector.
     * This a basically a heuristic and does not provide guaranteed good matchingparameters
     * @throws RuleException
     */
    private List<Term> createDefaultMatchingTerms() throws RuleException {
        try {
            this.term = getTerm();
        } catch (RuleException e) {
            e.printStackTrace();
        }
        List<Term> defaultMatchingTerms = new ArrayList<>();

        try {
            Term copy = this.term.accept(new EllipsisVisitor(), null);
            if(getTermSelector().isToplevel()) {
                //if its a toplevel term we can will try to just use the empty wildcar sequent or
                //use the toplevel term with only wildcards as parameters
                defaultMatchingTerms.add(new SchemaEllipsisTerm());
                defaultMatchingTerms.add(copy);
                if(getTerm().getSubterms().size() > 1) {
                    //if we have a nested term we try to remove the intermediate terms and just use toplevel and most inner term to match
                    Term innerTerm = getMostInnerTerm(getTerm());
                    innerTerm = new SchemaOccurTerm(innerTerm);
                    Term matchTerm = ReplaceVisitor.replace(term, new SubtermSelector(0), innerTerm);
                    defaultMatchingTerms.add(matchTerm);
                }
            } else {
                //if its not a toplevel term we either see if the wildcard version from above is unique in the sequent
                //or we try to use the parent term with wildcards
                TermSelector parentSelector = getParentSelector(getTermSelector());
                Term parentTerm = parentSelector.selectSubterm(sequent);
                parentTerm = parentTerm.accept(new ReplaceSubtermVisitor(), getTermSelector().getTermNo());
                defaultMatchingTerms.add(parentTerm);
                Term occurTerm = new SchemaOccurTerm(new SchemaCaptureTerm(matchKeyword, copy));
                defaultMatchingTerms.add(occurTerm);
            }
        } catch (TermBuildException e) {
            e.printStackTrace();
        }

        //we sort be the length of the match term. other sortings are possible and should be considered
        defaultMatchingTerms.sort(Comparator.comparingInt(term1 -> term1.toString().length()));
        return defaultMatchingTerms;
    }


    /**
     * Returns a schematicSequent representing this TermParameter.
     * If not already present, this sequent is obtained from the original representation.
     *
     * @return the schematic sequent representation of this term parameter
     * @throws RuleException
     */
    public Sequent getSchematicSequent() throws RuleException {
        if(schematicSequent != null) {
            return schematicSequent;
        }

        Sequent res = null;
        if(oSchematicTerm != null) {
            res = getUniqueSequent(oSchematicTerm, getTermSelector().getPolarity());
            if(res != null) {
                return res;
            }
            res = getUniqueSequent(new SchemaOccurTerm(oSchematicTerm), getTermSelector().getPolarity());
            if(res != null) {
                return res;
            }
        }

        List<Term> defaultMatchingTerms = createDefaultMatchingTerms();
        for(Term t : defaultMatchingTerms) {
            res = getUniqueSequent(t, getTermSelector().getPolarity());
            if(res != null) {
                schematicSequent = res;
                return res;
            }
        }

        if(termSelector != null) {
            schematicSequent = getUniqueMatchingTerm(sequent, termSelector);
            return schematicSequent;
        }

        schematicSequent = getUniqueMatchingTerm(sequent, term);
        return schematicSequent;
    }

    private Sequent getUniqueSequent(Term t, TermSelector.SequentPolarity polarity) {
        Sequent s = null;
        if(polarity.equals(SequentPolarity.ANTECEDENT)) {
            s = new Sequent(Collections.singletonList(new ProofFormula(t)), new ArrayList<>());
        } else {
            s = new Sequent(new ArrayList<>(), Collections.singletonList(new ProofFormula(t)));
        }
        SequentMatcher sequentMatcher = new SequentMatcher();
        ImmutableList<Matching> matchings = sequentMatcher.match(s, sequent);
        if (matchings.size() == 1) {
            return s;
        }
        return null;
    }

    /**
     * Returns the term that was given to the constructor, {@code null} if no
     * concrete term has been provided to the constructor.
     *
     * @return term as on initialisation, or {@code null}
     */
    public @Nullable Term getOriginalTerm() {
        return oterm;
    }

    /**
     * Returns the term selector that was given to the constructor, {@code null}
     * if no concrete term has been provided to the constructor.
     *
     * @return term selector as on initialisation, or {@code null}
     */
    public @Nullable TermSelector getOriginalTermSelector() {
        return oTermSelector;
    }

    /**
     * Returns the schematic sequent that was given to the constructor, {@code null}
     * if no concrete term has been provided to the constructor.
     *
     * @return schematic sequent as on initialisation, or {@code null}
     */
    public @Nullable Sequent getOriginalSchematicSequent() {
        return oSchematicSequent;
    }

    /**
     * Returns the schematic term that was given to the constructor, {@code null}
     * if no schematic term has been provided to the constructor.
     *
     * @return schematic term on initialisation, or {@code null}
     */
    public @Nullable Term getOriginalSchematicTerm() {
        return oSchematicTerm;
    }


    private static MatchingEntry getUniqueMatchingInSequent(Sequent schemaSeq, Sequent concreteSeq) throws RuleException {

        if (!containsMatchTerm(schemaSeq)) {
            int antesize = schemaSeq.getAntecedent().size();
            int postsize = schemaSeq.getSuccedent().size();
            int countFormulas = antesize + postsize;
            if (countFormulas != 1) {
                throw new RuleException("Schematic sequent must either contain '?match' or must contain a single formula");
            }
            ProofFormula single =
                    antesize == 1 ? schemaSeq.getAntecedent().get(0) :
                    schemaSeq.getSuccedent().get(0);
            SchemaCaptureTerm matchTerm = new SchemaCaptureTerm("?match", single.getTerm());
            ProofFormula matchFormula = new ProofFormula(matchTerm);
            if (antesize == 1) {
                schemaSeq = new Sequent(Collections.singleton(matchFormula), Collections.emptyList());
            } else {
                schemaSeq = new Sequent(Collections.emptyList(), Collections.singleton(matchFormula));
            }
        }

        SequentMatcher sequentMatcher = new SequentMatcher();
        ImmutableList<Matching> matchings = sequentMatcher.match(schemaSeq, concreteSeq);
        if (matchings.size() == 0) {
            // Debug.dumpSeq(schemaSeq);
            // Debug.dumpSeq(concreteSeq);
            throw new RuleException("Schematic sequent " + schemaSeq +
                    " does not match.");
        }
        if (matchings.size() > 1) {
            throw new RuleException("Schematic sequent " + schemaSeq +
                    " matches more than once.");
        }

        MatchingEntry m = matchings.get(0).get("?match");
        if(m == null) {
            throw new RuleException("No ?match variable was found in schematic term " + schemaSeq);
        }
        return m;
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

    private static boolean isTermSchematic(Term t) {
        Boolean b = t.accept(new IsSchematicVisitor(), null);
        return b.booleanValue();
    }

    private static boolean containsMatchTerm(Term t) {
        Boolean b = t.accept(new ContainsMatchTermVisitor(), null);
        return b.booleanValue();
    }

    private static boolean containsMatchTerm(Sequent s) {
        return s.getAntecedent().stream().anyMatch(pf -> containsMatchTerm(pf.getTerm())) ||
               s.getSuccedent().stream().anyMatch(pf -> containsMatchTerm(pf.getTerm()));
    }

    private static class ContainsMatchTermVisitor extends DefaultTermVisitor<Object, Boolean, NoExceptions> {

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
            for (Term t : schemaCaptureTerm.getSubterms()) {
                if( t.accept(this, arg)) {
                    return true;
                }
            }
            return Boolean.FALSE;
        }

        @Override
        public Boolean visit(SchemaVarTerm term, Object arg) throws NoExceptions {
            return term.getName().equals("?match");
        }

        @Override
        public Boolean visitSchemaTerm(SchemaTerm schemaTerm, Object arg) throws NoExceptions {
            return defaultVisit(schemaTerm, arg);
        }
    }

    private static class IsSchematicVisitor extends DefaultTermVisitor<Object, Boolean, NoExceptions> {

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

    private @NonNull TermSelector matchTermInSequentUniquely(Term schemaTerm, Sequent s) throws RuleException {
        TermMatcher tm = new TermMatcher();

        // Wrap term into occurrence to search it everywhere.
        schemaTerm = new SchemaOccurTerm(schemaTerm);

        // ts holds the result found so far.
        TermSelector ts = null;

        for(int i = 0; i < s.getAntecedent().size(); ++i) {
            ImmutableList<Matching> matches = tm.match(schemaTerm, s.getAntecedent().get(i).getTerm());
            if(matches.size() == 1 && ts == null) {
                ts = new TermSelector(SequentPolarity.ANTECEDENT, i, matches.get(0).get("?match").getSelector());
            } else if((matches.size() == 1 && ts != null) || matches.size() > 1) {
                throw new RuleException("Matching of term " + schemaTerm + " is ambiguous.");
            }
        }
        for(int i = 0; i < s.getSuccedent().size(); ++i) {
            ImmutableList<Matching> matches = tm.match(schemaTerm, s.getSuccedent().get(i).getTerm());
            if(matches.size() == 1 && ts == null) {
                ts = new TermSelector(SequentPolarity.SUCCEDENT, i, matches.get(0).get("?match").getSelector());
            } else if((matches.size() == 1 && ts != null) || matches.size() > 1) {
                throw new RuleException("Matching of term " + schemaTerm + " is ambiguous.");
            }
        }

        // TODO make NotApplicableexception once that is on master
        if (ts == null) {
            throw new RuleException("Term " + schemaTerm + " cannot be matched on sequent.");
        }

        return ts;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("TermParameter[");
        sb.append("originally a " +
                (oterm != null ? "term" : oSchematicTerm != null ? "schematic term" : oTermSelector != null ? "termselector" : "schematic sequent"));
        sb.append(", term = " + term);
        sb.append(", schematicTerm = " + schematicTerm);
        sb.append(", schematicSequent = " + schematicSequent);
        sb.append(", termSelector = " + termSelector);
        sb.append("]");
        return sb.toString();
    }

    private static class EllipsisVisitor implements TermVisitor<Void, Term, TermBuildException> {
        public Term visit(Term t) throws TermBuildException {
            if(t instanceof VariableTerm) {
                return visit((VariableTerm) t, null);
            }
            if(t instanceof QuantTerm) {
                return visit((QuantTerm) t, null);
            }
            if(t instanceof ApplTerm) {
                return visit((ApplTerm) t, null);
            }
            if(t instanceof LetTerm) {
                return visit((LetTerm) t, null);
            }
            if(t instanceof SchemaVarTerm) {
                return visit((SchemaVarTerm) t, null);
            }
            if(t instanceof SchemaOccurTerm) {
                return visit((SchemaOccurTerm) t, null);
            }
            if(t instanceof SchemaEllipsisTerm) {
                return visit((SchemaEllipsisTerm) t, null);
            }
            if(t instanceof SchemaCaptureTerm) {
                return visit((SchemaCaptureTerm) t, null);
            }
            throw new TermBuildException("Visited unkown Term-type.");
        }

        @Override
        public Term visit(VariableTerm variableTerm, Void arg) throws TermBuildException {
            return new VariableTerm(variableTerm.getName(), variableTerm.getSort());
        }

        @Override
        public Term visit(QuantTerm quantTerm, Void arg) throws TermBuildException {
            return new QuantTerm(quantTerm.getQuantifier(), (VariableTerm)visit(quantTerm.getBoundVar()), new SchemaEllipsisTerm());
        }

        @Override
        public Term visit(ApplTerm applTerm, Void arg) throws TermBuildException {
            List<Term> arguments = new ArrayList<>();
            for(Term t : applTerm.getSubterms()) {
                arguments.add(new SchemaEllipsisTerm());
            }
            return new ApplTerm(applTerm.getFunctionSymbol(), arguments);
        }

        @Override
        public Term visit(SchemaOccurTerm occurTerm, Void arg) throws TermBuildException {
            return new SchemaOccurTerm(new SchemaEllipsisTerm(), occurTerm.getSort());
        }

        @Override
        public Term visit(SchemaVarTerm schemaVarTerm, Void arg) throws TermBuildException {
            return new SchemaVarTerm(schemaVarTerm.getName(), schemaVarTerm.getSort());
        }

        @Override
        public Term visit(SchemaCaptureTerm schemaCaptureTerm, Void arg) throws TermBuildException {
            return new SchemaCaptureTerm(schemaCaptureTerm.getName(), new SchemaEllipsisTerm());
        }

        @Override
        public Term visitSchemaTerm(SchemaTerm schemaTerm, Void arg) throws TermBuildException {
            return visit(schemaTerm);
        }

        @Override
        public Term visit(LetTerm letTerm, Void arg) throws TermBuildException {
            List<Pair<VariableTerm, Term>> subs = new ArrayList<>();
            for(Pair<VariableTerm, Term> p : letTerm.getSubstitutions()) {
                subs.add(new Pair<VariableTerm, Term>((VariableTerm) visit(p.fst), visit(p.snd)));
            }
            return new LetTerm(subs, new SchemaEllipsisTerm());
        }
    }

    private static class ReplaceSubtermVisitor implements TermVisitor<Integer, Term, TermBuildException> {
        public Term visit(Term t, Integer arg) throws TermBuildException {
            if(t instanceof VariableTerm) {
                return visit((VariableTerm) t, arg);
            }
            if(t instanceof QuantTerm) {
                return visit((QuantTerm) t, arg);
            }
            if(t instanceof ApplTerm) {
                return visit((ApplTerm) t, arg);
            }
            if(t instanceof LetTerm) {
                return visit((LetTerm) t, arg);
            }
            if(t instanceof SchemaVarTerm) {
                return visit((SchemaVarTerm) t, arg);
            }
            if(t instanceof SchemaOccurTerm) {
                return visit((SchemaOccurTerm) t, arg);
            }
            if(t instanceof SchemaEllipsisTerm) {
                return visit((SchemaEllipsisTerm) t, arg);
            }
            if(t instanceof SchemaCaptureTerm) {
                return visit((SchemaCaptureTerm) t, arg);
            }
            throw new TermBuildException("Visited unkown Term-type.");
        }

        @Override
        public Term visit(VariableTerm variableTerm, Integer arg) throws TermBuildException {
            return new VariableTerm(variableTerm.getName(), variableTerm.getSort());
        }

        @Override
        public Term visit(QuantTerm quantTerm, Integer arg) throws TermBuildException {
            if(arg == 0) {
                return new QuantTerm(quantTerm.getQuantifier(), (VariableTerm)visit(quantTerm.getBoundVar(), -1), new SchemaCaptureTerm(matchKeyword, new SchemaEllipsisTerm()));
            }
            return new QuantTerm(quantTerm.getQuantifier(), (VariableTerm)visit(quantTerm.getBoundVar(), -1), new SchemaEllipsisTerm());
        }

        @Override
        public Term visit(ApplTerm applTerm, Integer arg) throws TermBuildException {
            List<Term> arguments = new ArrayList<>();
            for(int i = 0; i < applTerm.getSubterms().size(); ++i) {
                if(i == arg) {
                    arguments.add(new SchemaCaptureTerm(matchKeyword, new SchemaEllipsisTerm()));
                } else {
                    arguments.add(new SchemaEllipsisTerm());
                }
            }
            return new ApplTerm(applTerm.getFunctionSymbol(), arguments);
        }

        @Override
        public Term visit(SchemaOccurTerm occurTerm, Integer arg) throws TermBuildException {
            return new SchemaOccurTerm(new SchemaEllipsisTerm(), occurTerm.getSort());
        }

        @Override
        public Term visit(SchemaVarTerm schemaVarTerm, Integer arg) throws TermBuildException {
            return new SchemaVarTerm(schemaVarTerm.getName(), schemaVarTerm.getSort());
        }

        @Override
        public Term visit(SchemaCaptureTerm schemaCaptureTerm, Integer arg) throws TermBuildException {
            return new SchemaCaptureTerm(schemaCaptureTerm.getName(), new SchemaEllipsisTerm());
        }

        @Override
        public Term visitSchemaTerm(SchemaTerm schemaTerm, Integer arg) throws TermBuildException {
            return visit(schemaTerm, arg);
        }

        @Override
        public Term visit(LetTerm letTerm, Integer arg) throws TermBuildException {
            List<Pair<VariableTerm, Term>> subs = new ArrayList<>();
            for(Pair<VariableTerm, Term> p : letTerm.getSubstitutions()) {
                subs.add(new Pair<VariableTerm, Term>((VariableTerm) visit(p.fst, arg), visit(p.snd, arg)));
            }
            if(arg == 0) {
                return new LetTerm(subs, new SchemaCaptureTerm(matchKeyword, new SchemaEllipsisTerm()));
            } else {
                return new LetTerm(subs, new SchemaEllipsisTerm());
            }
        }
    }
}
