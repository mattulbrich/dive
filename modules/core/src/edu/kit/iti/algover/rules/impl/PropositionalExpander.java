package edu.kit.iti.algover.rules.impl;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Util;

public class PropositionalExpander {

    private List<Sequent> sequents;

    public boolean expand(ProofFormula formula, SequentPolarity polarity, boolean allowSplit) {
        ImmutableList<WorkSequent> expansion = expand(formula.getTerm(), polarity, allowSplit);

        List<Sequent> newSequents = new ArrayList<Sequent>();
        if (expansion.size() == 1) {
            WorkSequent elem = expansion.getHead();
            if (elem.antecedent.size() + elem.succedent.size() == 1) {
                return false;
            }
        }


        for (WorkSequent termSequent : expansion) {
            List<ProofFormula> ante = Util.map(termSequent.antecedent, x -> new ProofFormula(0, x));
            List<ProofFormula> succ = Util.map(termSequent.succedent, x -> new ProofFormula(0, x));
            Sequent s = new Sequent(ante, succ);
            for (Sequent sequent : sequents) {
                newSequents.add(sequent.union(s));
            }
        }

        sequents = newSequents;

        return true;
    }

    private Sequent singelSeq(ProofFormula formula, SequentPolarity polarity) {
        if (polarity == SequentPolarity.ANTECEDENT) {
            return Sequent.singleAntecedent(formula);
        } else {
            return Sequent.singleSuccedent(formula);
        }
    }

    /* package visible for testing */
    ImmutableList<WorkSequent> expand(Term formula, SequentPolarity polarity, boolean allowSplit) {

        if (is(formula, BuiltinSymbols.AND) && polarity == SequentPolarity.ANTECEDENT
                || is(formula, BuiltinSymbols.OR) && polarity == SequentPolarity.SUCCEDENT) {
            Term a1 = formula.getSubterms().get(0);
            Term a2 = formula.getSubterms().get(1);
            return union(expand(a1, polarity, allowSplit), expand(a2, polarity, allowSplit));
        }

        if (is(formula, BuiltinSymbols.IMP) && polarity == SequentPolarity.SUCCEDENT) {
            Term a1 = formula.getSubterms().get(0);
            Term a2 = formula.getSubterms().get(1);
            return union(expand(a1, polarity.getOpposite(), allowSplit),
                    expand(a2, polarity, allowSplit));
        }

        if (allowSplit) {
            if (is(formula, BuiltinSymbols.AND) && polarity == SequentPolarity.SUCCEDENT
                    || is(formula, BuiltinSymbols.OR) && polarity == SequentPolarity.ANTECEDENT) {
                Term a1 = formula.getSubterms().get(0);
                Term a2 = formula.getSubterms().get(1);
                return split(expand(a1, polarity, allowSplit), expand(a2, polarity, allowSplit));
            }

            if (is(formula, BuiltinSymbols.IMP) && polarity == SequentPolarity.ANTECEDENT) {
                Term a1 = formula.getSubterms().get(0);
                Term a2 = formula.getSubterms().get(1);
                return split(expand(a1, polarity.getOpposite(), allowSplit),
                        expand(a2, polarity, allowSplit));
            }
        }

        WorkSequent s = new WorkSequent();
        if (polarity == SequentPolarity.ANTECEDENT) {
            s.antecedent = ImmutableList.single(formula);
        } else {
            s.succedent = ImmutableList.single(formula);
        }

        return ImmutableList.single(s);
    }

    private ImmutableList<WorkSequent> split(
            ImmutableList<WorkSequent> list1,
            ImmutableList<WorkSequent> list2) {
        return list1.appendAll(list2);
    }

    private ImmutableList<WorkSequent> union(
            ImmutableList<WorkSequent> list1,
            ImmutableList<WorkSequent> list2) {

        ImmutableList<WorkSequent> result = ImmutableList.nil();
        for (WorkSequent s1 : list1) {
            for (WorkSequent s2 : list2) {
                WorkSequent s = new WorkSequent(s1, s2);
                result = result.append(s);
            }
        }

        return result;
    }

    /*
     * Is the formula an application term with function symbol fs?
     */
    private boolean is(Term formula, FunctionSymbol fs) {
        if (formula instanceof ApplTerm) {
            ApplTerm appl = (ApplTerm) formula;
            return appl.getFunctionSymbol() == fs;
        }
        return false;
    }

    public List<Sequent> getSequents() {
        return sequents;
    }

    /* package visible for testing */
    static class WorkSequent {
        private ImmutableList<Term> succedent;
        private ImmutableList<Term> antecedent;

        public WorkSequent(WorkSequent s1, WorkSequent s2) {
            this.antecedent = s1.antecedent.appendAll(s2.antecedent);
            this.succedent = s1.succedent.appendAll(s2.succedent);
        }

        public WorkSequent() {
            antecedent = ImmutableList.nil();
            succedent = ImmutableList.nil();
        }

        public WorkSequent addAntecedent(Term term) {
            antecedent = antecedent.append(term);
            return this;
        }

        public WorkSequent addSuccedent(Term term) {
            antecedent = antecedent.append(term);
            return this;
        }

        @Override
        public String toString() {
            return antecedent + " ==> " + succedent;
        }

    }


}
