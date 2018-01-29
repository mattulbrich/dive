/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.term.Term;

/**
 * This exception is used to indicate that a schematic term cannot be
 * matched against another type.
 *
 * This is one of the exceptions which could be thrown on a more regular basis
 * since it neatly implements a backtracking control flow during matching.
 *
 * @author mattias ulbrich
 */
@SuppressWarnings("serial")
public class MatchException extends Exception {

    private final Term schemaTerm;
    private final Term concreteTerm;

    public MatchException(Term schemaTerm, Term concreteTerm) {
        this.schemaTerm = schemaTerm;
        this.concreteTerm = concreteTerm;
    }

    public MatchException(Term schemaTerm, Term concreteTerm, Throwable cause) {
        this(schemaTerm, concreteTerm);
        initCause(cause);
    }

    public Term getSchemaTerm() {
        return schemaTerm;
    }

    public Term getConcreteTerm() {
        return concreteTerm;
    }

}
