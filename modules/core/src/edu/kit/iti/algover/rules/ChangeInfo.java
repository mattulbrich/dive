/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;

public class ChangeInfo {

    public static final List<ChangeInfo> UNCHANGED =
            Collections.singletonList(
                    new ChangeInfo(Sequent.EMPTY, Sequent.EMPTY, Collections.emptyList()));

    public static final List<ChangeInfo> CLOSE =
            Collections.emptyList();

    private final Sequent additions;
    private final Sequent deletions;
    private final List<Pair<TermSelector, Term>> replacements;

    public ChangeInfo(Sequent additions, Sequent deletions, List<Pair<TermSelector, Term>> replacements) {
        this.additions = additions;
        this.deletions = deletions;
        this.replacements = replacements;
    }

    public Sequent getAdditions() {
        return additions;
    }

    public Sequent getDeletions() {
        return deletions;
    }

    public List<Pair<TermSelector, Term>> getReplacements() {
        return Collections.unmodifiableList(replacements);
    }

}
