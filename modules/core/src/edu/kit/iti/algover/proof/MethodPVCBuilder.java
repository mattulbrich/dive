/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.LocalVarDecl;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.PVCSequenter;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.TreeUtil;

/**
 * Builder for {@link PVC} from a {@link DafnyMethod} and a {@link SymbexPath}.
 *
 * This class is not ready for multi-threading.
 *
 * @author Created by sarah on 8/18/16.
 * @author Revised by mattias on 8/27/17.
 * @see PVC
 */
public class MethodPVCBuilder implements PVCBuilder {

    /**
     * Path through program which represents state of this pvc
     */
    private SymbexPath pathThroughProgram;

    /**
     * The procedure that produces the {@link Sequent} for this builder.
     */
    private PVCSequenter sequenter;

    /**
     * DafnyMethid to which this PVC belongs
     */
    private DafnyMethod declaration;

    private SymbolTable symbolTable;

    private Sequent sequent;

    private Map<TermSelector, DafnyTree> referenceMap;

    public MethodPVCBuilder() { }

    public PVC build() throws TermBuildException {
        return new PVC(this);
    }

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public MethodPVCBuilder setPathThroughProgram(SymbexPath pathThroughProgram) {
        this.sequent = null;
        this.pathThroughProgram = pathThroughProgram;
        return this;
    }

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    public MethodPVCBuilder setDeclaration(DafnyMethod decl) {
        this.sequent = null;
        this.declaration = decl;
        return this;
    }

    public SymbolTable getSymbolTable() {
        if(symbolTable == null) {
            symbolTable = makeSymbolTable();
        }
        return symbolTable;
    }

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        DafnyMethod method = declaration;

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method.getRepresentation())) {
            String name = decl.getChild(0).toString();
            Sort sort = ASTUtil.toSort(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        for (LocalVarDecl lvd : pathThroughProgram.getDeclaredLocalVars()) {
            String name = lvd.getName();
            Sort sort = TreeUtil.toSort(lvd.getType());
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    public void ensureSequentExists() {
        if(sequent == null) {
            PVCSequenter sequenter = this.sequenter;
            if(sequenter == null) {
                if (PVCSequenter.INSTANCES.isEmpty()) {
                    throw new RuntimeException("There is no PVCSequenter loaded. Maybe you need to configure to load the META-INF.services.");
                }
                sequenter = PVCSequenter.INSTANCES.get(0);
            }

            try {
                this.referenceMap = new HashMap<TermSelector, DafnyTree>();
                this.sequent =
                        sequenter.translate(pathThroughProgram, getSymbolTable(), referenceMap);
            } catch (DafnyException e) {
                // FIXME TODO Auto-generated catch block
                throw new Error(e);
            }
        }
    }

    public Sequent getSequent() {
        ensureSequentExists();
        return sequent;
    }

    public Map<TermSelector, DafnyTree> getReferenceMap() {
        ensureSequentExists();
        return Collections.unmodifiableMap(referenceMap);
    }

    public PVCSequenter getSequenter() {
        return sequenter;
    }

    public void setSequenter(PVCSequenter sequenter) {
        this.sequent = null;
        this.sequenter = sequenter;
    }

}
