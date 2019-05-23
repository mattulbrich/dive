package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * This sequenter is a specialisation of an update sequenter.
 *
 * It removes all let-assignments which are irrelevant. An assignment is called
 * invariant if the assigned variable does not occur in the matrix of the
 * let-term.
 *
 * <p> For example: In the term
 * <pre>
 *     let x,y,z:=1,2,3 :: let a,b:=x,y :: a > 0
 * </pre>
 * z is irrelevant since it does never occur. x and y occur in the assignments
 * of the second (inner) let. However, since b is irrelevant, the assignment to
 * y is also irrelevant. This sequenter would return the following term (reduced
 * to the relevant assignments) as result:
 * <pre>
 *     let x := 1 :: let a := x :: a > 0.
 * </pre>
 *
 * @author Mattias Ulbrich
 */
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
    protected ProofFormula postProcess(ProofFormula formula, Map<Term, DafnyTree> referenceMap) throws TermBuildException {

        Term simplified = formula.getTerm().accept(new LetRemover(), null);
        return new ProofFormula(simplified, formula.getLabels());
    }

    private static class LetRemover extends DefaultTermVisitor<Void, Term, TermBuildException> {

        public static final RelevanceChecker RELEVANCE_CHECKER = new RelevanceChecker();

        @Override
        protected Term defaultVisit(Term term, Void arg) {
            return term;
        }

        @Override
        public Term visit(LetTerm term, Void arg) throws TermBuildException {
            List<Pair<VariableTerm, Term>> substs = term.getSubstitutions();
            List<Pair<VariableTerm, Term>> newsubsts = new ArrayList<>();

            Term matrix = term.getTerm(0);

            matrix = matrix.accept(this, null);

            for (Pair<VariableTerm, Term> subst : substs) {
                VariableTerm var = subst.fst;
                Boolean relevant = matrix.accept(RELEVANCE_CHECKER, var);
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
