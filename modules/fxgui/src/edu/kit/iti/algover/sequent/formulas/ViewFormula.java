package edu.kit.iti.algover.sequent.formulas;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;

import java.util.ArrayList;
import java.util.List;

/**
 * This class is the model for a Formula in the {@link edu.kit.iti.algover.sequent.SequentController}.
 *
 */
public class ViewFormula {

    /**
     * The index of this formula in the sequent.
     */
    protected final int indexInSequent;
    /**
     * The ToplevelTerm of this formula.
     */
    private final Term term;
    /**
     * The type of this ViewFormla (see {@link Type}).
     */
    private final Type type;
    /**
     * The polarity in the sequent of this formula.
     */
    private final TermSelector.SequentPolarity polarity;

    /**
     * The type of the formula which may be either newly added, removed, partly changed or unchanged.
     * This is used to style the formual accordingly
     */
    public enum Type {
        ADDED,
        DELETED,
        CHANGED,
        ORIGINAL
    }

    //Invariant changedTerms.size() > 0 <==> type == Type.CHANGED
    private final List<TermSelector> changedTerms;

    public ViewFormula(int indexInSequent, Term term, Type type, TermSelector.SequentPolarity polarity) {
        this.indexInSequent = indexInSequent;
        this.polarity = polarity;
        this.term = term;
        this.type = type;
        changedTerms = new ArrayList<>();
        assert getType() != Type.CHANGED;
    }

    public ViewFormula(int indexInSequent, Term term, Type type, TermSelector.SequentPolarity polarity, List<TermSelector> changedTerms) {
        this.indexInSequent = indexInSequent;
        this.term = term;
        this.polarity = polarity;
        this.type = type;
        this.changedTerms = changedTerms;
        //Invariant changedTerms.size() > 0 <==> type == Type.CHANGED
        assert (changedTerms.size() > 0 || type == Type.CHANGED) || (changedTerms.size() == 0 || type != Type.CHANGED);
    }

    public int getIndexInSequent() {
        return indexInSequent;
    }

    public Term getTerm() {
        return term;
    }

    public Type getType() { return type; }

    public List<TermSelector> getChangedTerms() {
        return changedTerms;
    }

    public TermSelector.SequentPolarity getPolarity() {
        return polarity;
    }

    /**
     * Creates a TopLevel-TermSelctor pointing to this formula.
     * @return the created termSelector
     */
    public TermSelector getTermSelector() {
        return new TermSelector(polarity, indexInSequent);
    }
}
