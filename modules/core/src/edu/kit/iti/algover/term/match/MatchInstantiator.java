/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.term.SchemaTerm;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * This class is used by {@link Matching} to instantiate a term.
 *
 * It is derivate of a {@link ReplacementVisitor} which only treats schema
 * variables specially.
 */
class MatchInstantiator extends ReplacementVisitor<Matching> {

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

    @Override
    public Term visitSchemaTerm(SchemaTerm schemaTerm, Matching arg) throws TermBuildException {
        throw new TermBuildException("Terms containing schematic entities cannot be instantiated");
    }

    /**
     * This is a singleton. Get the instance.
     *
     * @return the only instance of the class
     */
    public static MatchInstantiator getInstance() {
        return INSTANCE;
    }

}
