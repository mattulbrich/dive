/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;

public class MatchInstantiator extends ReplacementVisitor<Matching> {

    private static final MatchInstantiator INSTANCE = new MatchInstantiator();

    @Override
    public Term visit(SchemaVarTerm schemaVarTerm, Matching matching) throws TermBuildException {

        if(schemaVarTerm.hasName()) {
            String name = schemaVarTerm.getName();
            MatchingEntry entry = matching.get(name);
            if(entry != null) {
                return entry.getValue();
            }
        }

        return null;
    }

    public static MatchInstantiator getInstance() {
        return INSTANCE;
    }

}
