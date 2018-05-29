/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import nonnull.Nullable;

/**
 * A matching entry is a simple data object class which encapsulates an entry
 * into a {@link Matching} table.
 *
 * <p>It comprises the name of the schematic entity, the term value, the
 * selector where this can be found.
 *
 * @author Mattias Ulbrich
 * @see Matching
 */
public class MatchingEntry {

    private final String key;
    private final Term value;
    private final SubtermSelector selector;
    private int termNo;
    private @Nullable
    TermSelector.SequentPolarity polarity;


    public MatchingEntry(String key, Term value, SubtermSelector selector) {
        this.key = key;
        this.value = value;
        this.selector = selector;
    }

    public String getKey() {
        return key;
    }

    public Term getValue() {
        return value;
    }

    public SubtermSelector getSelector() {
        return selector;
    }

    @Override
    public String toString() {
        String sel;
        if (polarity != null) {
            sel = getTermSelector().toString();
        } else {
            sel = getSelector().toString();
        }
        return key + " => " + value + " / " + sel;
    }

    public @Nullable
    TermSelector getTermSelector() throws IllegalStateException {
        if (polarity != null)
            return new TermSelector(new TermSelector(this.polarity, this.termNo), this.getSelector());
        else
            throw new IllegalStateException("There is no Termselector present in this MatchingEntry");
    }

    /**
     * Refine the MatchingEntry by information from the toplevel formula the mathcingentry belomgs to
     *
     * @param polarity on which side of the sequent
     * @param termNo   which formula in the semisequent
     * @return MatchingEntry
     */
    public void refineContext(TermSelector.SequentPolarity polarity, int termNo) throws IllegalStateException {
        if (this.polarity == null) {
            this.polarity = polarity;
            this.termNo = termNo;
        }
    }
}
