/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;


import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.SchemaOccurTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Triple;

public class TermMatcher {

    private class Visitor implements TermVisitor<Triple<Term, Matching, SubtermSelector>, ImmutableList<Matching>, MatchException> {

        @Override
        public ImmutableList<Matching> visit(SchemaVarTerm schemaVarTerm, Triple<Term, Matching, SubtermSelector> arg) throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            if(schemaVarTerm.hasName()) {
                MatchingEntry entry = m.get(schemaVarTerm.getName());
                if(entry == null) {
                    return ImmutableList.single(m.add(schemaVarTerm.getName(), conc, sel));
                } else {
                    Term alreadyThere = entry.getValue();
                    if(!alreadyThere.equals(conc)) {
                        throw new MatchException(schemaVarTerm, conc);
                    } else {
                        return ImmutableList.single(m);
                    }
                }
            } else {
                return ImmutableList.single(m.addUnnamed(conc, sel));
            }
        }

        @Override
        public ImmutableList<Matching> visit(SchemaOccurTerm occurTerm, Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {

            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            Term innerTerm = occurTerm.getTerm(0);

            ImmutableList<Matching> result;
            try {
                result = innerTerm.accept(this, arg);
                result = result.map(x -> x.addEllipsis(conc, sel));
            } catch(MatchException ex) {
                // it's ok not to match!
                result = ImmutableList.nil();
            }

            for(int i = 0; i < conc.countTerms(); i++) {
                Term subTerm = conc.getTerm(i);
                SubtermSelector subSel = new SubtermSelector(sel, i);
                    result = result.appendAll(occurTerm.accept(this, new Triple<>(subTerm, m, subSel)));
            }

            return result;
        }

        @Override
        public ImmutableList<Matching> visit(VariableTerm varTerm, Triple<Term, Matching, SubtermSelector> arg) throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;

            if(varTerm.equals(conc)) {
                return ImmutableList.single(m);
            } else {
                throw new MatchException(varTerm, conc);
            }
        }

        @Override
        public ImmutableList<Matching> visit(ApplTerm applTerm, Triple<Term, Matching, SubtermSelector> arg) throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            if(applTerm.equals(conc)) {
                return ImmutableList.single(m);
            }

            if(!(conc instanceof ApplTerm)) {
                throw new MatchException(applTerm, conc);
            }

            ApplTerm applTerm2 = (ApplTerm) conc;

            FunctionSymbol f1 = applTerm.getFunctionSymbol();
            FunctionSymbol f2 = applTerm2.getFunctionSymbol();

            if(f1 != f2) {
                throw new MatchException(applTerm, conc);
            }

            ImmutableList<Matching> matchings = ImmutableList.single(m);
            for(int i = 0; i < f1.getArity(); i++) {
                Term subSchem = applTerm.getTerm(i);
                Term subConc = conc.getTerm(i);
                SubtermSelector subSel = new SubtermSelector(sel, i);
                matchings = matchings.flatMap(x ->
                    subSchem.accept(this, new Triple<>(subConc, x, subSel)));
            }

            return matchings;
        }

        @Override
        public ImmutableList<Matching> visit(QuantTerm quantTerm, Triple<Term, Matching, SubtermSelector> arg) throws MatchException {
            Matching m = arg.snd;
            Term conc = arg.fst;
            SubtermSelector sel = arg.trd;

            if(quantTerm.equals(conc)) {
                return ImmutableList.single(m);
            }

            if(!(conc instanceof QuantTerm)) {
                throw new MatchException(quantTerm, conc);
            }

            QuantTerm quantTerm2 = (QuantTerm) conc;

            Quantifier f1 = quantTerm.getQuantifier();
            Quantifier f2 = quantTerm2.getQuantifier();

            if(f1 != f2) {
                throw new Error();
            }

            // TODO allow matching bound variable, too.
            if(!quantTerm.getBoundVar().equals(quantTerm2.getBoundVar())) {
                throw new MatchException(quantTerm, conc);
            }

            Term subSchem = quantTerm.getTerm(0);
            Term subConc = conc.getTerm(0);
            SubtermSelector subSel = new SubtermSelector(sel, 0);

            return subSchem.accept(this, new Triple<>(subConc, m, subSel));
        }

        @Override
        public ImmutableList<Matching> visit(LetTerm letTerm, Triple<Term, Matching, SubtermSelector> arg)
                throws MatchException {
            throw new MatchException(letTerm, arg.fst);
        }


    }

    public ImmutableList<Matching> match(Term schematicTerm, Term concreteTerm) throws MatchException {
        return match(schematicTerm, concreteTerm, Matching.emptyMatching());
    }

    public ImmutableList<Matching> matchOccurrences(Term schematicTerm, Term concreteTerm) throws MatchException {
        return match(new SchemaOccurTerm(schematicTerm), concreteTerm);
    }

    private ImmutableList<Matching> match(Term schem, Term conc, Matching m) throws MatchException {
       return schem.accept(new Visitor(), new Triple<>(conc, m, new SubtermSelector()));
    }



}
