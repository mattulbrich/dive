/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

/**
 * Created by Philipp on 27.08.2017.
 */
public interface ReferenceVisitor<R> {

    R visit(CodeReference codeTarget);

    R visit(ProofTermReference termTarget);

    R visit(UserInputReference userInputTarget);
}
