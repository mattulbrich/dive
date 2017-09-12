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

public class MockPVCBuilder implements PVCBuilder {

    private SymbexPath pathThroughProgram;
    private DafnyDecl declaration;
    private Sequent sequece;
    private SymbolTable symboltable;

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public void setPathThroughProgram(SymbexPath pathThroughProgram) {
        this.pathThroughProgram = pathThroughProgram;
    }

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    public void setDeclaration(DafnyDecl declaration) {
        this.declaration = declaration;
    }

    public Sequent getSequent() {
        return sequece;
    }

    public void setSequent(Sequent sequece) {
        this.sequece = sequece;
    }

    public SymbolTable getSymbolTable() {
        return symboltable;
    }

    public void setSymbolTable(SymbolTable symboltable) {
        this.symboltable = symboltable;
    }

    public PVC build() {
        return new PVC(this);
    }

}
