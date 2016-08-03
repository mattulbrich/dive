/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

public interface TermVisitor<A, R> {

    R visit(VariableTerm variableTerm, A arg);

    R visit(SchemaVarTerm schemaVarTerm, A arg);

    R visit(QuantTerm quantTerm, A arg);

    R visit(ApplTerm applTerm, A arg);

    R visit(LetTerm letTerm, A arg);

}
