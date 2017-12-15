package edu.kit.iti.algover.sequent;

import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;

public class TopLevelFormula {

    public enum ChangeType {
        ADDED, MODIFIED, DELETED, ORIGINAL;
    }
    private final int indexInSequent;

    private final Term term;
    private final ChangeType changeType;

    public TopLevelFormula(int indexInSequent, Term term, ChangeType changeType) {
        this.indexInSequent = indexInSequent;
        this.term = term;
        this.changeType = changeType;
    }

    public TopLevelFormula(int indexInSequent, Term term) {
        this(indexInSequent, term, ChangeType.ORIGINAL);
    }

    public Term getTerm() {
        return term;
    }

    public ChangeType getChangeType() {
        return changeType;
    }

    public int getIndexInSequent() {
        return indexInSequent;
    }

}
