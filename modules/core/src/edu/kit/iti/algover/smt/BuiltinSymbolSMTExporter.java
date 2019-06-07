/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.smt;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smt.SExpr.Type;
import edu.kit.iti.algover.smt.SMTOperatorMap.OperatorEntry;
import edu.kit.iti.algover.smt.SMTOperatorMap.SMTExporter;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Term;

public class BuiltinSymbolSMTExporter implements SMTExporter {

    @Override
    public SExpr translate(OperatorEntry entry, SMTTrans trans, ApplTerm term) throws SMTException {
        String name = entry.getSmtFunction();
        Type[] args = entry.getArguments();
        List<SExpr> children = new ArrayList<>(term.countTerms());
        int i = 0;
        for (Term t : term.getSubterms()) {
            children.add(t.accept(trans, args[i++]));
        }

        return new SExpr(name, entry.getResult(), children);
    }
}
