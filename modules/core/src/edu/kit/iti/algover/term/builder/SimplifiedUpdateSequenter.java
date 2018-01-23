package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.List;

public class SimplifiedUpdateSequenter extends UpdateSequenter {

    @Override
    public String getName() {
        return "ass-simp";
    }

    @Override
    public String getDescriptiveName() {
        return "Sequence of relevant assignments in front of every formula";
    }

    @Override
    protected ProofFormula postProcess(ProofFormula formula) throws TermBuildException {

        Term simplified = formula.getTerm().accept(new LetRemover(), null);
        return new ProofFormula(simplified);

    }

    private static class LetRemover extends DefaultTermVisitor<Void, Term, TermBuildException> {

        @Override
        protected Term defaultVisit(Term term, Void arg) {
            return term;
        }

        @Override
        public Term visit(LetTerm term, Void arg) throws TermBuildException {
            List<Pair<VariableTerm, Term>> substs = term.getSubstitutions();
            List<Pair<VariableTerm, Term>> newsubsts = new ArrayList<>();

            Term matrix = term.getTerm(0);

            for (Pair<VariableTerm, Term> subst : substs) {
                VariableTerm var = subst.fst;
                Boolean relevant = matrix.accept(new RelevanceChecker(), var);
                if(relevant) {
                    newsubsts.add(subst);
                }
            }

            if(newsubsts.isEmpty())
                return matrix;

            return new LetTerm(newsubsts, matrix);
        }
    }

    private static class RelevanceChecker extends DefaultTermVisitor<VariableTerm, Boolean, RuntimeException> {

        @Override
        protected Boolean defaultVisit(Term term, VariableTerm arg) {
            return term.getSubterms().stream().anyMatch(x->x.accept(this, arg));
        }

        @Override
        public Boolean visit(VariableTerm term, VariableTerm arg) throws RuntimeException {
            return term.equals(arg);
        }

        @Override
        public Boolean visit(LetTerm term, VariableTerm arg) throws RuntimeException {
            boolean isTarget = term.getSubstitutions().stream()
                            .map(Pair::getFst).anyMatch(x -> x.equals(arg));

            if(isTarget) {
                // ignore the matrix if the variable is a target.
                List<Term> subs = term.getSubterms();
                return subs.subList(1, subs.size())
                        .stream().anyMatch(x->x.accept(this, arg));
            } else {
                return defaultVisit(term, arg);
            }
        }
    }
}
