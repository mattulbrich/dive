/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;

public class MatchingEntry {

    private final String key;
    private final Term value;
    private final SubtermSelector selector;

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
        return key + " => " + value + " / " + selector;
    }

}
