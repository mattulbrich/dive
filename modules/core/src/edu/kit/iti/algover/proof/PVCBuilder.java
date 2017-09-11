/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;

public interface PVCBuilder {

    SymbexPath getPathThroughProgram();

    DafnyDecl getDeclaration();

    Sequent getSequent();

    SymbolTable getSymbolTable();

}
