/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

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

    default R visitSchemaTerm(SchemaTerm occurTerm, A arg) throws E {
        throw new Error("The visitor of type " + getClass() +
                " must not be applied to schematic terms.");
    }

}
