/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import edu.kit.iti.algover.term.match.MatchException;

public interface TermVisitor<A, R, E extends Exception> {

    R visit(VariableTerm variableTerm, A arg) throws E;

    R visit(QuantTerm quantTerm, A arg) throws E;

    R visit(ApplTerm applTerm, A arg) throws E;

    R visit(LetTerm letTerm, A arg) throws E;

    default R visit(SchemaOccurTerm occurTerm, A arg) throws E {
        return visitSchemaTerm(occurTerm, arg);
    }

    default R visit(SchemaVarTerm schemaVarTerm, A arg) throws E {
        return visitSchemaTerm(schemaVarTerm, arg);
    }

    default R visit(SchemaCaptureTerm schemaCaptureTerm, A arg) throws E {
        return visitSchemaTerm(schemaCaptureTerm, arg);
    }

    default R visitSchemaTerm(SchemaTerm schemaTerm, A arg) throws E {
        throw new Error("The visitor of type " + getClass() +
                " must not be applied to schematic terms.");
    }

}
