/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;

public class Matching {

    private static final Matching EMPTY = new Matching(ImmutableList.nil());
    private final ImmutableList<MatchingEntry> entries;

    private Matching(ImmutableList<MatchingEntry> entries) {
        this.entries = entries;
    }

    public MatchingEntry get(String name) {
        for (MatchingEntry entry : entries) {
            if(entry.getKey().equals(name)) {
                return entry;
            }
        }
        return null;
    }

    public Matching add(MatchingEntry entry) {
        assert get(entry.getKey()) == null;

        return new Matching(entries.append(entry));
    }

    public Matching addUnnamed(Term value, SubtermSelector selector) {
        int no = 0;
        while(get("_" + no) != null) {
            no++;
        }
        return add(new MatchingEntry("_" + no, value, selector));
    }

    public Term instantiate(Term t) throws TermBuildException {
        Term result = t.accept(MatchInstantiator.getInstance(), this);
        if(result == null) {
            return t;
        } else {
            return result;
        }
    }

    public static Matching emptyMatching() {
        return EMPTY;
    }

    @Override
    public String toString() {
        return entries.toString();
    }

}
