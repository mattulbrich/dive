/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyClassBuilder;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;

import java.util.Map;

public class MockPVCBuilder implements PVCBuilder {

    private Project project;

    private SymbexPath pathThroughProgram;
    private DafnyDecl declaration;
    private Sequent sequece;
    private SymbolTable symboltable;
    private String pathIdentifier;

    private Map<TermSelector,DafnyTree> referenceMap;

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    @Override
    public DafnyDecl getDeclaration() {
        return declaration;
    }

    @Override
    public Map<TermSelector, DafnyTree> getReferenceMap() {
        return referenceMap;
    }

    public void setReferenceMap(Map<TermSelector, DafnyTree> referenceMap) {
        this.referenceMap = referenceMap;
    }

    @Override
    public String getPathIdentifier() {
        return pathIdentifier;
    }

    public void setPathIdentifier(String pathIdentifier) {
        this.pathIdentifier = pathIdentifier;
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

    public void setPathThroughProgram(SymbexPath pathThroughProgram) {
        this.pathThroughProgram = pathThroughProgram;
    }

    public void setSymbolTable(SymbolTable symboltable) {
        this.symboltable = symboltable;
    }

    @Override
    public Project getProject() {
        return this.project;
    }

    public void setProject(Project project) {
        this.project = project;
    }

    public PVC build() {
        return new PVC(this);
    }

}
