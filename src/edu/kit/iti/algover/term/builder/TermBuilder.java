package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Term;

public class TermBuilder {

    public static final Term negate(Term t) {
        return new ApplTerm(BuiltinSymbols.NEG, t);
    }

}
