/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;

import java.util.Map;

/**
 * Use an PVC builder to construct a {@link PVC}.
 *
 * It is passed to the constructor {@link PVC#PVC(PVCBuilder)}
 * where the elements are read.
 */
public interface PVCBuilder {

    SymbexPath getPathThroughProgram();

    DafnyDecl getDeclaration();

    Sequent getSequent();

    SymbolTable getSymbolTable();

    Map<TermSelector, DafnyTree> getReferenceMap();

    /**
     * Returns the path identifier for this pvc.
     *
     * Can be obtained from path through program for methods, but not
     * for functions.
     *
     * @return a locally unique non-null string
     */
    String getPathIdentifier();

    Project getProject();
}
